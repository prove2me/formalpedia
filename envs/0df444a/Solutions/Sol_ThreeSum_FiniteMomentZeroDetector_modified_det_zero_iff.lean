-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.modified_det_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:29.691978+00:00
-- url     : https://prove2.me/submissions/b9a73383-c970-4eff-b17f-6f92501be00a

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_support_ne_zero
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modified_det_factor

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) (a : ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) :
    (modifiedHankel v w a t).det=0 ↔ ∃ s, v s=a := by
  have hn := det_hankel_support_ne_zero v w hv hw
  rw [modified_det_factor,mul_eq_zero]
  simp only [hn,false_or,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,
    sq_eq_zero_iff,sub_eq_zero]
end ThreeSum.FiniteMomentZeroDetector
