-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:57.792924+00:00
-- url     : https://prove2.me/submissions/18b6f08b-23fd-4c45-9e9d-e91f9a4c7e4f

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) : C.cdf (fun _ => 1) = 1 := by
  have h : Iic (fun _ : Fin d => (1 : I)) = univ := by
    ext x
    simp [mem_Iic, Pi.le_def, unitInterval.le_one']
  simp [cdf, h]
end ProbabilityTheory.Copula
