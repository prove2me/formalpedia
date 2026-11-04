-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.det_hankel_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:24.206422+00:00
-- url     : https://prove2.me/submissions/9affb454-db41-480e-8dbb-e4eef1dfaf47

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_hankel_factor

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) :
    (hankel v w t).det=(vandermonde v).det^2 * ∏ s, w s := by
  rw [hankel_factor,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
  change (vandermonde v).det*(∏ s,w s)*(vandermonde v).det=_
  ring
end ThreeSum.FiniteMomentZeroDetector
