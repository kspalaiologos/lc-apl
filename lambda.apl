lam←{
     ⍝ TODO:
     ⍝ - Ability to select mode (lex/parse, beta-reduce)
     ⍝ - Showing steps of reduction (verbose mode)
     ⍝ - [DONE] Detecting terms with infinite expansion using hashes.
     ⍝ - More built-in functions.
     ⍝ - Integrated REPL.
     ⍝ - Delta-conversion of lambda terms if matching one was
     ⍝   found in the dictionary.
     ⎕IO⎕ML←1 1
     ∆d←⍪('true' ('Lam' (,'t') ('Lam' (,'f') ('Var' (,'t')))))
     ∆d,←('false' ('Lam' (,'t') ('Lam' (,'f') ('Var' (,'f')))))
     ⍺←∆d⋄∆t←⍺⋄∆hi←{∆t,←⍺⍵}⋄∆hr←{∆t∘←((∆t↑[2]⍨¯1∘+),∆t↓[2]⍨⊢)⍵⍳⍨,1↑∆t}⋄err←{⍵⎕SIGNAL 8}
     hash←{{1e10|⍺+31×⍵}/128+1(220⌶)⍵}⋄sd←'₀₁₂₃₄₅₆₇₈₉'⋄l←'()λ.='⋄ad←{⍺,sd[,1+10⊥⍣¯1⊢⍵]}
     str←{'Lam'≡⊃⍵:∊'(λ'(2⊃⍵)'. '(∇3⊃⍵)')'⋄'Var'≡⊃⍵:2⊃⍵⋄'App'≡⊃⍵:∊'('(∇2⊃⍵)' '(∇3⊃⍵)')'}
     lx←{0=≢⍵:⍬⋄(⊃⍵)∊l:(⊂0,⊃⍵),∇1↓⍵⋄3≠(⎕UCS 10 32)⍳⊃⍵:∇1↓⍵⋄'#'=⊃⍵:∇⍵↓⍨⍵⍳⎕UCS 10
         ×k←⊥⍨⌽⍵∊sd,⎕A,⎕C⎕A:(⊂1,k↑⍵),∇k↓⍵⋄err'eltoken'⍵}
     pr←{L←0'λ'⋄P←0'('⋄E←0'='⋄C←0')'⋄D←0'.'
         at←{P≡⊃⍵:{lx t←tr(1↓⍵)⋄C≢⊃lx:err'eparen'⋄(1↓lx) t}⍵
             1≡⊃⊃⍵:(1↓⍵)('Var'(1↓⊃⍵))⋄L≡⊃⍵:ab 1↓⍵⋄err'etoken'}
         ab←{i←⊥⍨⌽1=⊃¨⍵⋄i<1:err'elambda'⋄D≢⍵⊃⍨i+1:err'edot'
             lx tv←tr(1+i)↓⍵⋄nm←1↓¨i↑⍵⋄lx(nm{0=≢⍺:⍵⋄(¯1↓⍺)∇'Lam'(⊃⌽⍺)⍵}tv)}
         tr←{L≡⊃⍵:ab 1↓⍵⋄↑{(L≢⊃⍺)∧(1≢⊃⊃⍺)∧(P≢⊃⍺):⍺⍵⋄lx t←at ⍺⋄lx ∇'App'⍵ t}/at ⍵}
         bi←{k←⊃⍵⋄lx v←tr 2↓⍵⋄0≠≢lx:err'estray'⋄_←∆hr k⋄_←∆hi k v⋄⍬}
         E≡⊃1↓⍵:bi ⍵⋄⊃⌽tr ⍵}
     a←⍪''0⋄ac←{∆i←{i←(,1↑a)⍳⊂⍵⋄_←⍺{i>⊃⌽⍴a:a,←⍵ 0⋄a[2;i]+←⍺⋄0}⍵⋄⍵ad,a[2;i]}
         {'Var'≡⊃⍵:'Var' (0 ∆i ⊃⌽⍵)⋄'App'≡⊃⍵:'App' (∇2⊃⍵) (∇3⊃⍵)
          'Lam'≡⊃⍵:(⊂'Lam'),((∇3⊃⍵) ,⍨⍥⊂ (1 ∆i 2⊃⍵))}⍵}
     de←{lk←{(⊂⍵)∊⍺:'Var'⍵⋄i←(⊂⍵)⍳⍨,1↑∆t⋄i>⊃⌽⍴∆t:'Var'⍵⋄⊃∆t[2;i]}
         {⍺←⊂''⋄'Var'≡⊃⍵:(⍺ lk ⊃⌽⍵)⋄'App'≡⊃⍵:'App' (⍺∇2⊃⍵) (⍺∇3⊃⍵)
          'Lam'≡⊃⍵:(2↑⍵),⊂(⍺,⊂2⊃⍵)∇3⊃⍵}⍵}
     br←{'Lam'≡⊃⍵:(2↑⍵),⊂∇3⊃⍵⋄'Var'≡⊃⍵:⍵⋄'App'≢⊃⍵:err'eint'
         an bn←∇¨1↓⍵⋄'Lam'≢⊃an:⍵⋄an bn←1↓ac 'App' an bn⋄av←2⊃an
         {v←'Var'≡⊃⍵⋄v∧av≡2⊃⍵:bn⋄v:⍵⋄v←'Lam'≡⊃⍵⋄v∧av≡2⊃⍵:⍵⋄v:(2↑⍵),⊂∇3⊃⍵
          'App'≡⊃⍵:'App' (∇2⊃⍵) (∇3⊃⍵)}3⊃an}
     rd←{h←⍬⋄i←{⍵∊h:1⋄h,←⍵⋄0}⋄in←de ⍵⋄r←br⍣{(i hash ⍺)∨⍺≡⍵}in⋄(in≡r)∨(hash r)∊¯1↓h:err'einf'⋄r}
     ⍬≢ast←pr lx ⍵:str rd ast
 }
