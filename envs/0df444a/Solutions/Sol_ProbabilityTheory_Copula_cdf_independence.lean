-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_independence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:10.031029+00:00
-- url     : https://prove2.me/submissions/d80fca07-9eaa-46c1-a697-34c0cc5540f0

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
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


attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
namespace ProbabilityTheory.Copula
theorem _root_.solution {d : ℕ} (u : Fin d → I) :
    (independence d).cdf u = ∏ i, (u i : ℝ) := by
  have h : Iic u = Set.pi univ (fun i => Iic (u i)) := by
    ext x
    simp [mem_Iic, Pi.le_def]
  simp only [cdf, Measure.real, toMeasure_independence, h, Measure.pi_pi,
    unitInterval.volume_Iic, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (u i).property.1)
end ProbabilityTheory.Copula
