-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.levi_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:31.284855+00:00
-- url     : https://prove2.me/submissions/94ad708d-9eb3-4850-a3ce-a43ff8af52b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_levi_const
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul


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
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {ι : Type} [Fintype ι] (K c : ℝ) (f : (ι → ℂ) → ℝ) (z w : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) : levi (fun v => K + c * f v) z w = c * levi f z w := by
  rw [levi_add_smul c contDiffAt_const hf, levi_const, zero_add]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
