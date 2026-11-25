-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.sub_isBigO_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:06.792607+00:00
-- url     : https://prove2.me/submissions/d271d592-a2e5-4d4c-9d07-8af25a14711b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hD).toContinuousLinearEquiv
  have hE : ∀ x, E x = D x := by
    intro x
    rfl
  have h1 : (fun x => x - a) =O[𝓝 a] (fun x => D (x - a)) := by
    simpa [hE] using E.isBigO_sub_rev (𝓝 a) a
  have h3 : (fun x => D (x - a) - (q x - q a)) =o[𝓝 a] (fun x => D (x - a)) := by
    have := (hq.isLittleO.trans_isBigO h1).neg_left
    refine this.congr_left (fun x => ?_)
    abel
  have h4 := h3.right_isBigO_sub
  refine h1.trans (h4.congr_right (fun x => ?_))
  abel
end ReciprocityTheory.L2DbarEstimates.Y
