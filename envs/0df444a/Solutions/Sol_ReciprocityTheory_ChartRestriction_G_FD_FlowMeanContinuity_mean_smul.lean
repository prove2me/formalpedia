-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.mean_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:33.413193+00:00
-- url     : https://prove2.me/submissions/67b8fc53-734a-40d4-94ac-719d093c7a5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity

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
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ENNReal) (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (s : Set α) (F : α → ℂ) :
    (((c • μ) s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂(c • μ) = ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Measure.restrict_smul, integral_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, Complex.ofReal_mul, mul_inv, Complex.real_smul]
  calc _ = ((μ s).toReal : ℂ)⁻¹ * (∫ y in s, F y ∂μ) *
        (((c.toReal : ℝ) : ℂ)⁻¹ * ((c.toReal : ℝ) : ℂ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc', mul_one]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
