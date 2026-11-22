-- Prove2me | solution 1 for ProbabilityTheory.Copula.isSklarCopula_ofContinuousMarginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:43.533619+00:00
-- url     : https://prove2.me/submissions/549977f3-9f93-43ba-bc79-c97725d05048

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
public import Theorems.Thm_ProbabilityTheory_Copula_monotone_cdf
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    IsSklarCopula μ (ofContinuousMarginals μ hc) := by
  intro x
  rw [cdf, ofContinuousMarginals, toMeasure_ofMap,
    map_measureReal_apply (measurable_marginalTransform μ) measurableSet_Iic]
  have heq (i : Fin d) : {z : Fin d → ℝ | z i ≤ x i} =ᵐ[μ.toMeasure]
      {z | marginalTransform μ z i ≤ marginalTransform μ x i} := by
    apply ae_eq_of_subset_of_measure_ge
    · intro z hz
      exact ProbabilityTheory.monotone_cdf (marginal μ i) hz
    · have hleft : μ.toMeasure {z | z i ≤ x i} =
          ENNReal.ofReal (ProbabilityTheory.cdf (marginal μ i) (x i)) := by
        rw [ProbabilityTheory.ofReal_cdf]
        exact (Measure.map_apply (measurable_pi_apply i) measurableSet_Iic).symm
      have hright : μ.toMeasure {z | marginalTransform μ z i ≤ marginalTransform μ x i} =
          ENNReal.ofReal (ProbabilityTheory.cdf (marginal μ i) (x i)) := by
        have hm : Measurable (fun z => marginalTransform μ z i) :=
          (measurable_pi_apply i).comp (measurable_marginalTransform μ)
        change μ.toMeasure ((fun z => marginalTransform μ z i) ⁻¹'
          Iic (marginalTransform μ x i)) = _
        rw [← Measure.map_apply hm measurableSet_Iic, map_marginalTransform_eval μ hc,
          unitInterval.volume_Iic]
        rfl
      rw [hleft, hright]
    · exact (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet
    · exact measure_ne_top _ _
  apply measureReal_congr
  apply Filter.Eventually.set_eq
  filter_upwards [ae_all_iff.mpr (fun i => (heq i).mem_iff)] with z hz
  change (∀ i, marginalTransform μ z i ≤ marginalTransform μ x i) ↔ ∀ i, z i ≤ x i
  exact forall_congr' (fun i => (hz i).symm)
end ProbabilityTheory.Copula
