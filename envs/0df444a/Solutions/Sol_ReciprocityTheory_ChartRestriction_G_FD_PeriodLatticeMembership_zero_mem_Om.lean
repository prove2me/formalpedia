-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.zero_mem_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:52.675297+00:00
-- url     : https://prove2.me/submissions/4c8ae4ea-0c16-420f-a68b-2a6b0795989b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients

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
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) : (0 : Fin (Fintype.card X.Ψ) → ℝ) ∈ Om ξ x ω := by
  show (fun τ => ∑ j, (0 : Fin (Fintype.card X.Ψ) → ℝ) j * ω j τ) ∈ admissibleImaginary X ξ x
  simp only [admissibleImaginary, Set.mem_setOf_eq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero,
    Complex.ofReal_zero, zero_smul, add_zero]
  intro τ i
  exact (hx τ).2 i
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
