-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.line_deriv_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:33.152803+00:00
-- url     : https://prove2.me/submissions/cbcaf7b8-3e70-4f06-a856-b137498b76f4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => φ (z + s • w)) (fderiv ℝ φ (z + s • w) w) s := by
  have hc : Continuous (fun s : ℝ => z + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), z + s • w ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hz)
  filter_upwards [hev] with s hs
  have hd : DifferentiableAt ℝ φ (z + s • w) :=
    (hφ.differentiableOn two_ne_zero).differentiableAt (hU.mem_nhds hs)
  exact hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line z w s)
end ReciprocityTheory.AnForm.A
