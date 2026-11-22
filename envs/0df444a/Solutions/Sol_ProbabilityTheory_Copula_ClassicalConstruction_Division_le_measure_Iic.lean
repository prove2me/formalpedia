-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.Division.le_measure_Iic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:56:01.661872+00:00
-- url     : https://prove2.me/submissions/4ac75ea8-0905-4676-a7a1-36fe5c12def0

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_clip_le
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
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_eq_zero_of_eq
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
theorem _root_.solution (hF : IsClassical F) (D : Division a b) {ε : ℝ}
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε))
    (u w : Fin d → I) (hw : ∀ i, w i = 0 ∨ (w i : ℝ) + ε ≤ (u i : ℝ)) :
    ENNReal.ofReal (rectangleIncrement F (a ⊓ w) (b ⊓ w)) ≤ D.measure F (Iic u) := by
  induction D with
  | @leaf a b hab =>
    by_cases hb : b ≤ u
    · simpa only [measure, Measure.smul_apply, measurableSet_Iic, Measure.dirac_apply', mem_Iic, hb,
      indicator_of_mem, Pi.one_apply, smul_eq_mul,
      mul_one] using ENNReal.ofReal_le_ofReal (hF.rectangleIncrement_clip_le a b w hab)
    · obtain ⟨i, hi⟩ := not_forall.mp hb
      have hib : (u i : ℝ) < (b i : ℝ) := not_le.mp hi
      have he : (a ⊓ w) i = (b ⊓ w) i := by
        change min (a i) (w i) = min (b i) (w i)
        rcases hw i with hz | hw
        · simp only [hz, zero_le, inf_of_le_right]
        · have hwa : w i ≤ a i := by
            change (w i : ℝ) ≤ (a i : ℝ)
            have := hmesh i
            linarith
          rw [min_eq_right hwa, min_eq_right (hwa.trans (hab i))]
      rw [rectangleIncrement_eq_zero_of_eq _ _ i he, ENNReal.ofReal_zero]
      exact bot_le
  | @cut a b i t hat htb left right ihl ihr =>
    rw [measure, Measure.add_apply, clip_cut a b w i t,
      ENNReal.ofReal_add (hF.increasing _ _ (inf_le_inf left.ordered le_rfl))
        (hF.increasing _ _ (inf_le_inf right.ordered le_rfl))]
    exact add_le_add (ihl hmesh.1) (ihr hmesh.2)
end ProbabilityTheory.Copula.ClassicalConstruction.Division
