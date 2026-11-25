-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.logDens_cdAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:27.250233+00:00
-- url     : https://prove2.me/submissions/5d61df4c-28e3-42fb-8c74-07ee088861fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_log_densF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_cpt_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_Lm_cpt_cdAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem contDiff_det_mat_cpt (x0 : Frame X.Ψ r) (τ : X.Ψ) :
    ContDiff ℂ ∞ fun w : V (nd X) => (mat (cpt X x0 w) τ).det := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  refine ContDiff.sum (fun σ _ => contDiff_const.mul ?_)
  first
  | exact contDiff_prod (fun j _ => cpt_entry_cd X x0 τ _ _)
  | fun_prop
private theorem eventually_mem_omF (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ∀ᶠ w in 𝓝 z, w ∈ OmF X x0 := by
  have hz' : cpt X x0 z ∈ X.dom := hz
  show ∀ᶠ w in 𝓝 z, cpt X x0 w ∈ X.dom
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hz' ⊢
  rw [Filter.eventually_all]
  intro τ
  refine Filter.Eventually.and ?_ ?_
  · have hc : Continuous fun w : V (nd X) => (mat (cpt X x0 w) τ).det :=
      (contDiff_det_mat_cpt X x0 τ).continuous
    exact hc.continuousAt.eventually_ne (hz' τ).1
  · rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun w : V (nd X) => psgn X.p0 i * (dmin X.Gm (cpt X x0 w) τ i).re :=
      continuous_const.mul (Complex.continuous_re.comp (dmin_cpt_cd X x0 τ i).continuous)
    exact hc.continuousAt.eventually (Ioi_mem_nhds ((hz' τ).2 i))
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z := by
  refine ContDiffAt.congr_of_eventuallyEq ?_
    ((eventually_mem_omF X x0 hz).mono (fun w hw => log_densF_eq X x0 hw))
  exact ContDiffAt.sum (fun τ _ => ContDiffAt.sum (fun i _ =>
    contDiffAt_const.mul (Lm_cpt_cdAt X x0 hz τ _)))
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
