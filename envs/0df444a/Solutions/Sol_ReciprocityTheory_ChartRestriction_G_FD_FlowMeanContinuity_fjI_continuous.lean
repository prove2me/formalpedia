-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.fjI_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:15.42318+00:00
-- url     : https://prove2.me/submissions/62930cc4-fcf2-450e-8372-ca6bfc3070d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMeanContinuity_flow_differentiable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_flow_mem_dom_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_flowMat_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
theorem _root_.solution (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous (fjI X ξ ν P x) := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hc1 : Continuous (fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    (flow_differentiable X ξ x).continuous.comp
      (continuous_pi fun τ => Complex.continuous_ofReal.comp (continuous_apply τ))
  have hc2 : Continuous (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x)) :=
    hP.1.continuousOn.comp_continuous hc1 hmaps
  unfold fjI
  exact hc2.mul (by fun_prop)
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
