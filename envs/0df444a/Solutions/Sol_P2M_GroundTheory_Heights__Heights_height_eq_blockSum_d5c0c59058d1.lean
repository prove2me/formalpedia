-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:57.064588+00:00
-- url     : https://prove2.me/submissions/f63a1ab8-7cb0-4ab6-a7fe-216993960919

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (hx : BlockNonzero x) :
    height A x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      (∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k +
        ∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))) := by
  have hfin : ∀ k, (Function.support (blockFin (coordVec x) k)).Finite :=
    fun k ↦ finite_support_blockFin _ k (coordVec_ne_zero hx k)
  have hF : (∑ᶠ v : FinitePlace (coordField x),
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) =
      ∑ k, (A.deg k : ℝ) * ∑ᶠ v, blockFin (coordVec x) k v := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [mul_finsum]
      rfl
    · intro k _
      exact (hfin k).subset (Function.support_mul_subset_right _ _)
  have hA : ∀ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i)) =
      metricDefect A (fun k i ↦ σ (coordVec x k i)) +
        ∑ k, (A.deg k : ℝ) * Real.log (l2Norm fun i ↦ σ (coordVec x k i)) := by
    intro σ
    unfold metricDefect
    ring
  have hB : ∑ σ : coordField x →+* ℂ,
      ∑ k, (A.deg k : ℝ) * Real.log (l2Norm fun i ↦ σ (coordVec x k i)) =
      ∑ k, (A.deg k : ℝ) * ∑ σ : coordField x →+* ℂ, Real.log (l2Norm fun i ↦ σ (coordVec x k i)) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold height
  rw [hF, Finset.sum_congr rfl fun σ _ ↦ hA σ, Finset.sum_add_distrib, hB]
  unfold blockSum
  simp only [mul_add, Finset.sum_add_distrib]
  ring
end GroundTheory.Heights₂.Heights
