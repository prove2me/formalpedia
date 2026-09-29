-- Prove2me | solution 1 for WeinbergLeptons.eq12_zMass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:17:28.813689+00:00
-- url     : https://prove2.me/submissions/f19e92f5-7ce0-47fd-80c5-758fb65a98fe

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) :
    massSqMatrix g g' lam *ᵥ zVec g g' = (zMass g g' lam ^ 2) • zVec g g' := by
  have hN2 : Real.sqrt (g ^ 2 + g' ^ 2) ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (by positivity)
  ext i
  fin_cases i <;>
    simp [massSqMatrix, zVec, zMass, mulVec, dotProduct, Fin.sum_univ_four]
  · linear_combination (-(lam ^ 2 / 4) * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * g) * hN2
  · linear_combination (-(lam ^ 2 / 4) * (Real.sqrt (g ^ 2 + g' ^ 2))⁻¹ * g') * hN2
