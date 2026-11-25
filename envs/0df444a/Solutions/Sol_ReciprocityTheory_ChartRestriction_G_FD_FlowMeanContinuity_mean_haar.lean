-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.mean_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:04.593833+00:00
-- url     : https://prove2.me/submissions/e8a3bf26-0f58-4d1d-8c29-905ea936f529

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMeanContinuity_mean_smul

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
theorem _root_.solution {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (s : Set G) (F : G → ℂ) :
    ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ = ((ν s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂ν := by
  haveI : ProperSpace G := FiniteDimensional.proper_real G
  have h := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  rw [h, ENNReal.smul_def]
  exact (mean_smul μ _ (ENNReal.coe_ne_zero.mpr hpos.ne') ENNReal.coe_ne_top s F).symm
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
