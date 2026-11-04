-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.det_hankel_support_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:07.367963+00:00
-- url     : https://prove2.me/submissions/655b10e0-77f0-4d17-9352-3119e72ad2bf

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_formula

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) :
    (hankel v w t).det≠0 := by
  rw [det_hankel_formula]
  exact mul_ne_zero (pow_ne_zero 2 (Matrix.det_vandermonde_ne_zero_iff.mpr hv))
    (Finset.prod_ne_zero_iff.mpr (fun s hs => hw s))
end ThreeSum.FiniteMomentZeroDetector
