-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.modified_det_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:30.523103+00:00
-- url     : https://prove2.me/submissions/995d0f44-a147-4e6c-a8e3-47eb63bb4856

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_formula
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modifiedHankel_eq

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) :
    (modifiedHankel v w a t).det=(hankel v w t).det * ∏ s, (v s-a)^2 := by
  rw [modifiedHankel_eq,det_hankel_formula,det_hankel_formula,Finset.prod_mul_distrib]
  ring
end ThreeSum.FiniteMomentZeroDetector
