-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_bias_coupling_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:54:51.729161+00:00
-- url     : https://prove2.me/submissions/e201583f-9fb4-48f7-8a67-3db45cf535a4

import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_coupling_product_law
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators ENNReal

theorem solution (d : ℕ) (S : Finset (Fin d)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) :
    (∫ xs : Fin d → ℝ × ℝ, K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
       ∂(Measure.pi fun _ : Fin d => π)) =
    ∫ xs : Fin d → ℝ, (∏ i, if i ∈ S then max (xs i) 0 else 1) * K xs
       ∂(Measure.pi fun _ : Fin d => μ) := by
  let P := fun xs : Fin d → ℝ × ℝ => fun i => if i ∈ S then (xs i).2 else (xs i).1
  let ρ := fun xs : Fin d → ℝ => ∏ i, if i ∈ S then max (xs i) 0 else 1
  have hP : Measurable P := by
    apply measurable_pi_lambda
    intro i
    dsimp [P]
    split_ifs <;> fun_prop
  have hρ : Measurable ρ := by
    dsimp [ρ]
    apply Finset.measurable_prod
    intro i hi
    split_ifs <;> fun_prop
  have hρ0 (xs : Fin d → ℝ) : 0 ≤ ρ xs := by
    dsimp [ρ]
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact le_max_right _ _
    · norm_num
  change (∫ xs, K (P xs) ∂(Measure.pi fun _ : Fin d => π)) =
    ∫ xs, ρ xs * K xs ∂(Measure.pi fun _ : Fin d => μ)
  rw [← integral_map hP.aemeasurable hK.aestronglyMeasurable]
  rw [size_bias_coupling_product_law d S μ hint hpos π hfst hsnd]
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xs => by simp only [ENNReal.toReal_ofReal (hρ0 xs), smul_eq_mul])
