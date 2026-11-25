-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_logMap_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:31.641851+00:00
-- url     : https://prove2.me/submissions/cf50de97-63a7-4da8-a307-25d09ddcf6e8

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : mixedSpace E, (∀ i, |ucoord x i| < 1) →
    ∀ w : {w : InfinitePlace E // w ≠ w₀}, |logMap x w| ≤ B := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) with hb
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun x hx w => ?_⟩
  have hsum : (∑ i, ucoord x i • b i) = logMap x := by
    simpa [ucoord, hb] using b.sum_repr (logMap x)
  calc |logMap x w| = ‖logMap x w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖logMap x‖ := norm_le_pi_norm (logMap x) w
    _ = ‖∑ i, ucoord x i • b i‖ := by rw [hsum]
    _ ≤ ∑ i, ‖ucoord x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [_root_.norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx i).le
end ReciprocityTheory.Cheb
