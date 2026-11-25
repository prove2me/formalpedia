-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.contDiff_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:52.105695+00:00
-- url     : https://prove2.me/submissions/ef9f1b9d-ab10-4d1e-b5b3-1ee9a2dd504f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_Gnz

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
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution : ContDiff ℝ 2 (fn hm D Y) := by
  have h := cd_det (fun v : Fin 1 → ℂ => Gnz hm D Y (v 0)) (fun a b => cd_Gnz hm D Y a b)
  exact Complex.reCLM.contDiff.comp h
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
