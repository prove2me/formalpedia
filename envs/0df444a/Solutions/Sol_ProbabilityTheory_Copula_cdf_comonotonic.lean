-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_comonotonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:10.561661+00:00
-- url     : https://prove2.me/submissions/b97e12d8-aac1-4673-98da-069efe8d5ee1

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap


attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
namespace ProbabilityTheory.Copula
theorem _root_.solution {d : ℕ} (u : Fin d → I) :
    (comonotonic d).cdf u = ((⨅ i, u i : I) : ℝ) := by
  have h : (fun t (_ : Fin d) => t) ⁻¹' Set.Iic u = Set.Iic (⨅ i, u i) := by
    ext t
    simp [Set.mem_Iic, Pi.le_def, le_iInf_iff]
  have hdiag : Measurable (fun (t : I) (_ : Fin d) => t) :=
    measurable_pi_iff.mpr fun _ => measurable_id
  rw [cdf, toMeasure_comonotonic, map_measureReal_apply hdiag measurableSet_Iic, h]
  simp [Measure.real, (iInf u).property.1]
end ProbabilityTheory.Copula
