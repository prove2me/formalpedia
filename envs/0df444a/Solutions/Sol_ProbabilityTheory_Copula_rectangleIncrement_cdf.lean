-- Prove2me | solution 1 for ProbabilityTheory.Copula.rectangleIncrement_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:51:21.183367+00:00
-- url     : https://prove2.me/submissions/c983b7e5-c2ca-469d-94ad-1f0bd685a33f

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_cdf
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


attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement C.cdf a b = C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) := by
  rw [rectangleIncrement, partialIncrement_cdf C a b _ hab]
  congr 1
  ext x
  simp only [mem_ofPred_eq, Finset.mem_univ, forall_const, mem_univ_pi, mem_Ioc, Pi.le_def]
  exact ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩
end ProbabilityTheory.Copula
