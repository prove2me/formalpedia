-- Prove2me | solution 1 for closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:36.4605+00:00
-- url     : https://prove2.me/submissions/2d398636-c0c9-4c34-b6ac-7e561896e145

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
import Theorems.Thm_inner_sub_smul_one_apply_self


set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • 1‖ ≤ R) :
    closure (numericalRange A) ⊆ Metric.closedBall c R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    norm (⟪x, A x⟫_ℂ - c) = norm ⟪x, (A - c • 1) x⟫_ℂ := by
      rw [inner_sub_smul_one_apply_self A c hx]
    _ ≤ ‖x‖ * ‖(A - c • 1) x‖ := norm_inner_le_norm x _
    _ = ‖(A - c • 1) x‖ := by rw [hx, one_mul]
    _ ≤ ‖A - c • 1‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - c • 1‖ := by rw [hx, mul_one]
    _ ≤ R := hA
