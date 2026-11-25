-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:01.013471+00:00
-- url     : https://prove2.me/submissions/64e0b13b-526f-4cf9-81aa-ba2a4f8656fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f


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
open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A B : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    height (A.mul B) x = height A x + height B x := by
  have hA := finite_support_height A x hx
  have hB := finite_support_height B x hx
  have hfin : (∑ᶠ v : FinitePlace (coordField x),
      ∑ k, ((A.mul B).deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) =
      (∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) +
      ∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (B.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i)) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun v ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [HermLine.mul, Pi.add_apply, Int.cast_add]
    ring
  have hinf : (∑ σ : coordField x →+* ℂ,
      Real.log ((A.mul B).metric fun k i ↦ σ (coordVec x k i))) =
      (∑ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i))) +
      ∑ σ : coordField x →+* ℂ, Real.log (B.metric fun k i ↦ σ (coordVec x k i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    exact Real.log_mul (A.metric_pos _ (blockNonzero_sigma hx σ)).ne'
      (B.metric_pos _ (blockNonzero_sigma hx σ)).ne'
  unfold height
  rw [hfin, hinf]
  ring
end GroundTheory.Heights₂.Heights
