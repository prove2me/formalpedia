-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.cdf_probability_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:56:46.540761+00:00
-- url     : https://prove2.me/submissions/15249961-9eed-470c-90a2-8e7c6f9aa7c5

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_measure_Iic_le
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_le_measure_Iic
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_zero_lower
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_sub_le_sum_of_le
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_ext
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
namespace ProbabilityTheory.Copula.ClassicalConstruction
theorem _root_.solution (hF : IsClassical F)
    (D : Division (fun _ : Fin d => 0) (fun _ => 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hmesh : D.All (fun a b => ∀ i, (b i : ℝ) - (a i : ℝ) ≤ ε)) (u : Fin d → I) :
    F u - (d : ℝ) * ε ≤ (probability hF D).toMeasure.real (Iic u) ∧
      (probability hF D).toMeasure.real (Iic u) ≤ F u := by
  have hnonneg (v : Fin d → I) : 0 ≤ F v := by
    rw [← hF.rectangleIncrement_zero_lower]
    exact hF.increasing _ _ (fun i => (v i).property.1)
  have hzero (v : Fin d → I) : (fun _ => (0 : I)) ⊓ v = fun _ => 0 := by
    funext i; exact min_eq_left (v i).property.1
  have hone (v : Fin d → I) : (fun _ => (1 : I)) ⊓ v = v := by
    funext i; exact min_eq_right (v i).property.2
  have hupper : (probability hF D).toMeasure (Iic u) ≤ ENNReal.ofReal (F u) := by
    change D.measure F (Iic u) ≤ _
    simpa only [hzero, hone, hF.rectangleIncrement_zero_lower] using
      D.measure_Iic_le hF u
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  rw [ENNReal.toReal_ofReal (hnonneg u)] at hu
  refine ⟨?_, hu⟩
  let w : Fin d → I := fun i => ⟨max ((u i : ℝ) - ε) 0, le_max_right _ _,
    max_le (by linarith [(u i).property.2]) zero_le_one⟩
  have hw (i : Fin d) : w i = 0 ∨ (w i : ℝ) + ε ≤ (u i : ℝ) := by
    by_cases hi : (u i : ℝ) ≤ ε
    · left; apply Subtype.ext; exact max_eq_right (sub_nonpos.mpr hi)
    · right; dsimp [w]; rw [max_eq_left (sub_nonneg.mpr (not_le.mp hi).le)]; linarith
  have hwle : w ≤ u := by
    intro i
    change max ((u i : ℝ) - ε) 0 ≤ (u i : ℝ)
    exact max_le (sub_le_self _ hε) (u i).property.1
  have hlower : ENNReal.ofReal (F w) ≤ (probability hF D).toMeasure (Iic u) := by
    change _ ≤ D.measure F (Iic u)
    simpa only [hzero, hone, hF.rectangleIncrement_zero_lower] using
      D.le_measure_Iic hF hmesh u w hw
  have hl := ENNReal.toReal_mono (measure_ne_top (probability hF D).toMeasure _) hlower
  rw [ENNReal.toReal_ofReal (hnonneg w)] at hl
  have hs := hF.sub_le_sum_of_le w u hwle
  have he : ∑ i, ((u i : ℝ) - (w i : ℝ)) ≤ (d : ℝ) * ε := by
    calc
      _ ≤ ∑ _ : Fin d, ε := Finset.sum_le_sum (fun i _ => by
        dsimp [w]
        have := le_max_left ((u i : ℝ) - ε) 0
        linarith)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change F w ≤ (probability hF D).toMeasure.real (Iic u) at hl
  linarith
end ProbabilityTheory.Copula.ClassicalConstruction
