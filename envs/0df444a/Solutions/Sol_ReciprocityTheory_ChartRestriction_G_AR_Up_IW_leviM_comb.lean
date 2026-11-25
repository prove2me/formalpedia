-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.leviM_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:54.638521+00:00
-- url     : https://prove2.me/submissions/f6ab9011-7f6b-4e05-a2fd-db6230db848e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_kapW_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_dmin_cpt_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_cpt_cdAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_logDens_cdAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_comb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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
private theorem leviV_sub_sub_const_mul_of_eventuallyEq {n : ℕ} (f f1 f2 f3 : V n → ℂ) (c : ℂ) (z : V n) (ξ : Fin n → ℂ)
    (hev : f =ᶠ[𝓝 z] fun w => f1 w - f2 w - c * f3 w)
    (h1 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f1 w) (h2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f2 w)
    (h3 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ f3 w) :
    leviV n f z ξ = leviV n f1 z ξ - leviV n f2 z ξ - c * leviV n f3 z ξ := by
  have hle1 : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact mod_cast le_top
    | simp
  have hle2 : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by
    rw [one_add_one_eq_two]
    first
    | exact WithTop.coe_le_coe.mpr le_top
    | exact (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
    | exact mod_cast le_top
    | simp
    | decide
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one hle1).ne'
  have hD : ∀ᶠ w in 𝓝 z, fderiv ℝ f w = fderiv ℝ f1 w - fderiv ℝ f2 w - c • fderiv ℝ f3 w := by
    filter_upwards [hev.eventuallyEq_nhds, h1, h2, h3] with w hw hw1 hw2 hw3
    rw [hw.fderiv_eq]
    exact (((hw1.differentiableAt hn0).hasFDerivAt.sub (hw2.differentiableAt hn0).hasFDerivAt).sub
      ((hw3.differentiableAt hn0).hasFDerivAt.const_mul c)).fderiv
  have hW : ∀ l, wdb n l f =ᶠ[𝓝 z] fun w => wdb n l f1 w - wdb n l f2 w - c * wdb n l f3 w := by
    intro l
    filter_upwards [hD] with w hw
    simp only [wdb, hw, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hWd : ∀ g : V n → ℂ, (∀ᶠ w in 𝓝 z, ContDiffAt ℝ ∞ g w) → ∀ l,
      DifferentiableAt ℝ (wdb n l g) z := by
    intro g hg l
    have hf' : DifferentiableAt ℝ (fderiv ℝ g) z :=
      ((hg.self_of_nhds).fderiv_right hle2).differentiableAt one_ne_zero
    have hv : ∀ v : V n, DifferentiableAt ℝ (fun y => fderiv ℝ g y v) z :=
      fun v => hf'.clm_apply (differentiableAt_const v)
    have hsum : DifferentiableAt ℝ (fun y => fderiv ℝ g y (bas n l) +
        Complex.I * fderiv ℝ g y (Complex.I • bas n l)) z :=
      (hv _).add ((hv _).const_mul Complex.I)
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas n l) +
      Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) z
    simp only [div_eq_mul_inv]
    exact hsum.mul_const _
  have hwd : ∀ j l, wd n j (wdb n l f) z =
      wd n j (wdb n l f1) z - wd n j (wdb n l f2) z - c * wd n j (wdb n l f3) z := by
    intro j l
    have d1 := hWd f1 h1 l
    have d2 := hWd f2 h2 l
    have d3 := hWd f3 h3 l
    have e2 : fderiv ℝ (fun w => wdb n l f1 w - wdb n l f2 w - c * wdb n l f3 w) z =
        fderiv ℝ (wdb n l f1) z - fderiv ℝ (wdb n l f2) z - c • fderiv ℝ (wdb n l f3) z :=
      ((d1.hasFDerivAt.sub d2.hasFDerivAt).sub (d3.hasFDerivAt.const_mul c)).fderiv
    unfold wd
    rw [(hW l).fderiv_eq, e2]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold leviV
  simp only [hwd]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring
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
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (la1 la2 : Wt X.Ψ r) (k : ℕ) (ξ : Fin (nd X) → ℂ) :
    leviM X (phla X (la1 - kapW X - k • la2)) x0 z ξ =
      leviO X x0 (phla X la1) z ξ - leviDens X x0 z ξ - k * leviO X x0 (phla X la2) z ξ := by
  unfold leviO leviDens leviM
  have hev := eventually_mem_omF X x0 hz
  rw [leviV_sub_sub_const_mul_of_eventuallyEq (fun w => ((phla X (la1 - kapW X - k • la2) (cpt X x0 w) : ℝ) : ℂ))
      (fun w => ((phla X la1 (cpt X x0 w) : ℝ) : ℂ)) (fun w => ((Real.log (densF X x0 w) : ℝ) : ℂ))
      (fun w => ((phla X la2 (cpt X x0 w) : ℝ) : ℂ)) (k : ℂ) z ξ ?_ ?_ ?_ ?_]
  · first
    | (simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
        sub_zero]; done)
    | simp
  · filter_upwards [hev] with w hw
    have hw' : cpt X x0 w ∈ X.dom := hw
    try dsimp only
    rw [phla_comb X hw' la1 la2 k, phla_kapW_cpt X x0 ho hw]
    push_cast
    try ring
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (phla_cpt_cdAt X x0 hw la1)
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (logDens_cdAt X x0 hw)
  · filter_upwards [hev] with w hw
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp w (phla_cpt_cdAt X x0 hw la2)
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
