-- Prove2me | solution 1 for PalomarZF207.sigma1_sound_consistent
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:52:31.399016+00:00
-- url     : https://prove2.me/submissions/33dd67ff-d3a7-49f3-b791-ddaae086e4ce

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

open PalomarZF207
open PalomarZF207History

theorem solution : ArithmeticSigma1Sound → Consistent := by
  intro hSound hBot
  let φ : SigmaFormula := .atom .zero .zero true false
  have hBound : φ.bound 0 := ⟨trivial, trivial⟩
  have hRep : RepresentsArithmetic φ .bot := by
    refine ⟨trivial, ?_⟩
    intro V E _ hModel s env _
    constructor
    · intro hFalse
      exact False.elim hFalse
    · rintro ⟨a, b, ha, hb, hne⟩
      have hExtAxiom : Axiom fixedExt :=
        Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have hExt := hModel fixedExt hExtAxiom s
      have hab : a = b := hExt a b
        (fun z hz => False.elim (ha z hz))
        (fun z hz => False.elim (hb z hz))
      exact hne hab
  have hNat : φ.natEval (fun _ => 0) := hSound φ hBound .bot hRep hBot (fun _ => 0)
  exact hNat rfl
