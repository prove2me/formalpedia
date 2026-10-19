-- Prove2me | solution 1 for QuantumEcon.Duopoly.prop2_instance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:21:45.280995+00:00
-- url     : https://prove2.me/submissions/fc8c8d80-8c86-405a-88a2-9a061009e8f0

import Mathlib
import Definitions.Def_QuantumEcon_Duopoly_Setting

set_option autoImplicit false
open QuantumEcon.Duopoly

theorem solution:
    let P : Params := ⟨20, 2, 1, 10, 8⟩
    Standing P ∧ Lemma1Cond P ∧ P.B₂ < P.B₁ ∧
      prop2Threshold P = 107 / 15 ∧
      xStar₁ P = 102 / 109 ∧ xStar₂ P = 89 / 109 := by
  intro P
  norm_num [P, Standing, Lemma1Cond, aStar, Bh₁, Bh₂, Bhh, prop2Threshold, xStar₁, xStar₂, Fden, max_lt_iff]
