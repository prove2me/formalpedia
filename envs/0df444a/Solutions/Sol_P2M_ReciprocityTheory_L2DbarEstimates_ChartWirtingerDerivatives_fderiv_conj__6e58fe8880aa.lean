-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:36.324126+00:00
-- url     : https://prove2.me/submissions/31aaec1c-24f4-4625-87d3-6954cf78188f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution (n : ℕ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) y v = (starRingEnd ℂ) (fderiv ℝ g y v) := by
  have h : (fun w => (starRingEnd ℂ) (g w)) = Complex.conjLIE ∘ g := by
    funext w
    simp [Complex.conjLIE_apply]
  rw [h, LinearIsometryEquiv.comp_fderiv]
  simp
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
