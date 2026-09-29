-- Prove2me | solution 1 for WeinbergLeptons.eq13_photonMass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:15:35.375246+00:00
-- url     : https://prove2.me/submissions/5b10d559-d995-46db-ab4b-71c21820e606

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) :
    massSqMatrix g g' lam *ᵥ photonVec g g' = 0 := by
  ext i
  fin_cases i <;>
    simp [massSqMatrix, photonVec, mulVec, dotProduct, Fin.sum_univ_four] <;> ring
