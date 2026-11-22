-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.Division.measure_Iic_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:55:06.372774+00:00
-- url     : https://prove2.me/submissions/14321b77-65bc-468b-b8fc-4dacceb94d52

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
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
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_split
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


section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
namespace ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ClassicalConstruction
namespace Division
variable {a b : Fin d → I}
private theorem clip_cut (a b u : Fin d → I) (i : Fin d) (t : I) :
    rectangleIncrement F (a ⊓ u) (b ⊓ u) =
      rectangleIncrement F (a ⊓ u) (Function.update b i t ⊓ u) +
        rectangleIncrement F (Function.update a i t ⊓ u) (b ⊓ u) := by
  have he (x : Fin d → I) : Function.update x i t ⊓ u =
      Function.update (x ⊓ u) i (min t (u i)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp only [Pi.inf_apply, Function.update_self]
    · simp only [Pi.inf_apply, Function.update_of_ne hj]
  rw [he, he]
  exact rectangleIncrement_split _ _ _ _
end Division
end ClassicalConstruction
end ProbabilityTheory.Copula
end
end

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
theorem _root_.solution (hF : IsClassical F) (D : Division a b) (u : Fin d → I) :
    D.measure F (Iic u) ≤ ENNReal.ofReal (rectangleIncrement F (a ⊓ u) (b ⊓ u)) := by
  induction D with
  | @leaf a b hab =>
    by_cases hb : b ≤ u
    · simp only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one, inf_eq_left.mpr (hab.trans hb),
      inf_of_le_left, Std.le_refl]
    · simp only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      not_false_eq_true, indicator_of_notMem, smul_eq_mul, mul_zero, zero_le]
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, clip_cut a b u i t,
      ENNReal.ofReal_add (hF.increasing _ _ (inf_le_inf left.ordered le_rfl))
        (hF.increasing _ _ (inf_le_inf right.ordered le_rfl))]
    exact add_le_add ihl ihr
end ProbabilityTheory.Copula.ClassicalConstruction.Division
