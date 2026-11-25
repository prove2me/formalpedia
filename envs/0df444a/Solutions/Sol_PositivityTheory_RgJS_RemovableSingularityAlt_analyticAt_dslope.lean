-- Prove2me | solution 1 for PositivityTheory.RgJS.RemovableSingularityAlt.analyticAt_dslope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:23.050481+00:00
-- url     : https://prove2.me/submissions/26fa65dd-7f42-442f-8054-7369a65c5a17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.RemovableSingularityAlt
namespace PositivityTheory.RgJS.RemovableSingularityAlt
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f 1) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f 1) z := by
  rcases eq_or_ne z 1 with rfl | hne
  · have hev := h1.eventually_analyticAt
    have hd : DifferentiableOn ℂ f {w | AnalyticAt ℂ f w} := fun w hw => hw.differentiableAt.differentiableWithinAt
    have hs : {w | AnalyticAt ℂ f w} ∈ 𝓝 (1 : ℂ) := hev
    exact ((Complex.differentiableOn_dslope hs).2 hd).analyticAt hs
  · have hsl : AnalyticAt ℂ (fun w => (w - 1)⁻¹ • (f w - f 1)) z :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hne)).smul (hz.sub analyticAt_const)
    refine hsl.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hne] with w hw
    rw [dslope_of_ne _ hw, slope_def_module]
end PositivityTheory.RgJS.RemovableSingularityAlt
