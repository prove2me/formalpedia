-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.Om_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:23.313842+00:00
-- url     : https://prove2.me/submissions/d3b2d242-414c-4cfc-9a86-e75bf5d7fd76

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
theorem _root_.solution (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    IsOpen (Om ξ x ω) := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun b : Fin (Fintype.card X.Ψ) → ℝ =>
      psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ) +
        ((2 * X.c τ * ∑ j, b j * ω j τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re := by
    intro τ i
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    unfold lminor
    refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
    first
      | fun_prop
      | exact continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const))).smul
          continuous_const)
  have hO : Om ξ x ω = ⋂ (τ : X.Ψ), ⋂ (i : Fin (r + 1)), {b | 0 < psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ) +
        ((2 * X.c τ * ∑ j, b j * ω j τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re} := by
    ext b
    simp only [Om, admissibleImaginary, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hO]
  exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (hc τ i)
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
