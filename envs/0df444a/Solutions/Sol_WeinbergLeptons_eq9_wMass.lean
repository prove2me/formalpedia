-- Prove2me | solution 1 for WeinbergLeptons.eq9_wMass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:25:09.069482+00:00
-- url     : https://prove2.me/submissions/4985ae20-c8de-415a-b593-028468403479

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) :
    (massSqMatrix g g' lam).map (fun x : ℝ => (x : ℂ)) *ᵥ wVec = ((wMass g lam : ℂ) ^ 2) • wVec := by
  ext i
  fin_cases i <;>
    simp [massSqMatrix, wVec, wMass, mulVec, dotProduct, Fin.sum_univ_four] <;> ring
