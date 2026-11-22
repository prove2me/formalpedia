-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.Division.grid_mesh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:56:03.34123+00:00
-- url     : https://prove2.me/submissions/ab8911ab-2fbe-4055-b01e-596ff0230732

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_All_mono
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_comonotonic
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_independence
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty
attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic
attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
open ProbabilityTheory.Copula.ClassicalConstruction
open ProbabilityTheory.Copula.ClassicalConstruction.Division
variable {a b : Fin d → I}
namespace ProbabilityTheory.Copula.ClassicalConstruction.Division
theorem _root_.solution (l : List (Fin d)) (a b : Fin d → I) (hab : a ≤ b) :
    (grid l a b hab).All (fun x y => ∀ i,
      (y i : ℝ) - (x i : ℝ) ≤ ((b i : ℝ) - (a i : ℝ)) * (1 / 2 : ℝ) ^ l.count i) := by
  induction l generalizing a b with
  | nil => simp only [one_div, List.count_nil, pow_zero, mul_one, tsub_le_iff_right, grid, All,
    sub_add_cancel, Std.le_refl, implies_true]
  | cons j l ih =>
    dsimp only [grid, All]
    constructor
    all_goals
      apply (ih _ _ _).mono
      intro x y hxy i
      apply (hxy i).trans_eq
      by_cases hij : i = j
      · subst i; simp only [Function.update_self, List.count_cons_self, pow_succ]; ring
      · simp only [Function.update_of_ne hij, List.count_cons_of_ne (Ne.symm hij)]
end ProbabilityTheory.Copula.ClassicalConstruction.Division
