-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_update_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:47:25.277172+00:00
-- url     : https://prove2.me/submissions/8f9fbd18-f7e6-4043-9da4-c971df33bb83

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap


attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (i : Fin d) (u : I) :
    C.cdf (Function.update (fun _ => 1) i u) = (u : ℝ) := by
  have h : Iic (Function.update (fun _ : Fin d => (1 : I)) i u) =
      {x | x i ≤ u} := by
    ext x
    constructor
    · intro hx
      simpa using hx i
    · intro hx j
      by_cases hji : j = i
      · subst j
        simpa using hx
      · simpa [Function.update_of_ne hji] using (unitInterval.le_one' (t := x j))
  rw [cdf, h, C.measureReal_eval_le]
end ProbabilityTheory.Copula
