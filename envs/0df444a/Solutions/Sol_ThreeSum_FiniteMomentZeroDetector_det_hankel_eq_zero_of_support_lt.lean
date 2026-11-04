-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.det_hankel_eq_zero_of_support_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:25.536577+00:00
-- url     : https://prove2.me/submissions/b0adc3a2-9648-4e29-b73d-fd00f3ba45ae

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
theorem _root_.solution {t d : ℕ} (v w : Fin t → ℤ) (ht : t<d) :
    (hankel v w d).det=0 := by
  by_contra hdet
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hb : (hankel v w d).rank≤t := by
    rw [hankel_factor]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _))
  simp only [Fintype.card_fin] at hr
  omega
end ThreeSum.FiniteMomentZeroDetector
