-- Prove2me | solution 1 for SteinbergFalse.Counterexample.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T16:02:38.899881+00:00
-- url     : https://prove2.me/submissions/ebaedbab-f23d-406e-920c-a37c633673ad

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle
import Definitions.Def_SteinbergFalse_Counterexample_G
import Theorems.Thm_SteinbergFalse_Counterexample_G_isPlanar
import Theorems.Thm_SteinbergFalse_Counterexample_G_noFourFiveCycle
import Theorems.Thm_SteinbergFalse_Counterexample_G_not_colorable

/-!
Theorem 3 of Cohen-Addad, Hebdige, Kral', Li, Salgado (2017): the explicit 166-vertex graph `G`
is a witness. Planarity (`G_isPlanar`), absence of 4- and 5-cycles (`G_noFourFiveCycle`) and
non-3-colourability (`G_not_colorable`) are the three existing sibling theorems of the family.
-/

set_option autoImplicit false

open SteinbergFalse.Counterexample in
theorem solution :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      OPG37357.IsPlanar H ∧ NoFourFiveCycle H ∧ ¬ H.Colorable 3 := by
  exact ⟨166, G, G_isPlanar, G_noFourFiveCycle, G_not_colorable⟩
