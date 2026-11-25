-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.norm_sq_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:12.466312+00:00
-- url     : https://prove2.me/submissions/ad720bba-2784-4cbe-bda6-3bb6e248c036

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (L : V n →L[ℂ] ℂ) :
    ‖L‖ ^ 2 = ∑ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 := by

  set v : V n := (InnerProductSpace.toDual ℂ (V n)).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by
    rw [hv, LinearIsometryEquiv.norm_map]
  have hco : ∀ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ = ‖v j‖ := by
    intro j
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
    simp
  rw [hL, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [hco]
end ReciprocityTheory.L2DbarEstimates.C
