-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_ucoord_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:44.756336+00:00
-- url     : https://prove2.me/submissions/37392a70-5c55-4d04-ae9b-201003eaafc5

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : mixedSpace E,
    ∑ i, |ucoord x i - ucoord y i| ≤ A * ‖logMap x - logMap y‖ := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  refine ⟨∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun x y => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ucoord x i - ucoord y i =
      LinearMap.toContinuousLinearMap (b.coord i) (logMap x - logMap y) := by
    simp [ucoord, b, Module.Basis.coord_apply, map_sub]
  rw [h, ← Real.norm_eq_abs]
  exact ContinuousLinearMap.le_opNorm _ _
end ReciprocityTheory.Cheb
