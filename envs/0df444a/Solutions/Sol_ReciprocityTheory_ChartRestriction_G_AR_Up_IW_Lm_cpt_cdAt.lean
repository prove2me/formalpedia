-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Lm_cpt_cdAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:32.679683+00:00
-- url     : https://prove2.me/submissions/a2d442e8-6b30-4e4b-b1b0-243e2430f84e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_cpt_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_log_norm_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiffAt ℝ ∞ (fun w => Lm X (cpt X x0 w) τ i) z := by
  have hd : dmin X.Gm (cpt X x0 z) τ i ≠ 0 := dmin_ne_zero X hz τ i
  have hf := dmin_cpt_cd X x0 τ i
  have hre : ContDiff ℝ ∞ fun w => (dmin X.Gm (cpt X x0 w) τ i).re := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ fun w => (dmin X.Gm (cpt X x0 w) τ i).im := Complex.imCLM.contDiff.comp hf
  simp only [Lm, log_norm_eq, Complex.normSq_apply]
  refine ContDiffAt.div_const ?_ 2
  refine ((hre.mul hre).add (him.mul him)).contDiffAt.log ?_
  rw [← Complex.normSq_apply]
  exact (Complex.normSq_pos.mpr hd).ne'
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
