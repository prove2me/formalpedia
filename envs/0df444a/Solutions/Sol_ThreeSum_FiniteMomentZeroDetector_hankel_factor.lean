-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.hankel_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:23.429658+00:00
-- url     : https://prove2.me/submissions/a94d236f-04d7-48bb-8d23-460126393b9b

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) (d : ℕ) :
    hankel v w d=(powerTable v d)ᵀ * diagonal w * powerTable v d := by
  ext i j
  change (∑ s, w s * v s^(i.val+j.val))=
    ∑ s, (((powerTable v d)ᵀ * diagonal w) i s) * powerTable v d s j
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,powerTable]
  apply Finset.sum_congr rfl
  intro s hs
  rw [pow_add]
  ring
end ThreeSum.FiniteMomentZeroDetector
