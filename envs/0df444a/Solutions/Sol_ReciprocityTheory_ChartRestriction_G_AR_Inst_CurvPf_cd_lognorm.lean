-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lognorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:29.899407+00:00
-- url     : https://prove2.me/submissions/2e145732-1dba-48ab-94fe-beac3d2e6ca8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoefNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (d : F → ℂ) (hd : ContDiff ℝ 2 d)
    (z : F) (hz : d z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log ‖d w‖) z := by
  have h1 : ContDiffAt ℝ 2 (fun w => ‖d w‖) z := (hd.contDiffAt).norm ℝ hz
  exact h1.log (norm_ne_zero_iff.mpr hz)
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
