-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.hline_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:36.676262+00:00
-- url     : https://prove2.me/submissions/efdd38ed-eb60-42ec-ba23-c3eb99019aca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PeriodLatticeMembership_flow_mem_of_tube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
variable {X}
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
theorem _root_.solution {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube (Fintype.card X.Ψ) (Om ξ x ω)) := by
  have hF : Differentiable ℂ (fun t : Fin (Fintype.card X.Ψ) → ℂ =>
      X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x) := by
    rw [differentiable_pi]
    intro τ
    rw [differentiable_pi]
    intro a
    rw [differentiable_pi]
    intro b
    simp only [Data.flow, Data.flowMat, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hP.comp hF.differentiableOn (fun t ht => flow_mem_of_tube hξ hx ω ht)
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
