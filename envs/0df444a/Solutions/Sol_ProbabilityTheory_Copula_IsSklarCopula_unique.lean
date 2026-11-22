-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsSklarCopula.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:50:08.944353+00:00
-- url     : https://prove2.me/submissions/093d21fd-eaa1-43fb-b98c-8ef8d33446dc

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_injective
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_continuous_cdf
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
public import Theorems.Thm_ProbabilityTheory_coe_cdfUnit
public import Theorems.Thm_ProbabilityTheory_exists_cdf_eq_of_continuous
attribute [local fun_prop] ProbabilityTheory.Copula.continuous_cdf
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap
attribute [local simp] ProbabilityTheory.coe_cdfUnit


section
public section
open MeasureTheory Set Filter
open scoped unitInterval
namespace ProbabilityTheory.Copula
variable {d : ℕ}
private theorem denseRange_cdfUnit (μ : Measure ℝ) (hc : Continuous (ProbabilityTheory.cdf μ)) :
    DenseRange (cdfUnit μ) := by
  have hd : Dense (Ioo (0 : I) 1) := by
    rw [dense_iff_closure_eq, closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    ext u
    simp [unitInterval.le_one']
  apply hd.mono
  intro u hu
  obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc
    (show 0 < (u : ℝ) from hu.1) (show (u : ℝ) < 1 from hu.2)
  exact ⟨x, Subtype.ext hx⟩
end ProbabilityTheory.Copula
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
namespace IsSklarCopula
theorem _root_.solution {μ : ProbabilityMeasure (Fin d → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) : C = D := by
  apply cdf_injective
  have hd : DenseRange (marginalTransform μ) :=
    DenseRange.piMap (fun i => denseRange_cdfUnit (marginal μ i) (hc i))
  apply hd.equalizer C.continuous_cdf D.continuous_cdf
  funext x
  exact (hC x).trans (hD x).symm
end IsSklarCopula
end ProbabilityTheory.Copula
