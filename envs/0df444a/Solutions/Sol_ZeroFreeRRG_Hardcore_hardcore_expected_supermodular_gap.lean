-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_expected_supermodular_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:37:48.727107+00:00
-- url     : https://prove2.me/submissions/83acbd79-1ab8-46c8-8782-a4c4e45ad1e0

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_log_product_supermodular_gap
import Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_strict_product_event
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

theorem solution (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (horder : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2)
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1})
    (hI : let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
      Integrable (fun xs => g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅))
        (Measure.pi fun _ : Fin d => π)) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
    0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π) := by
  classical
  dsimp only at hI ⊢
  let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
    Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
  let gap := fun xs : Fin d → ℝ × ℝ => g xs Finset.univ-g xs ∅-∑ i, (g xs {i}-g xs ∅)
  let μ := Measure.pi fun _ : Fin d => π
  have hgood : ∀ᵐ xs ∂μ, ∀ a, 0 ≤ (xs a).1 ∧ (xs a).1 ≤ (xs a).2 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => horder)
  have hnonneg : 0 ≤ᵐ[μ] gap := by
    filter_upwards [hgood] with xs hx
    have hh := (hardcore_log_product_supermodular_gap θ hθ.le (fun a => (xs a).1)
      (fun a => (xs a).2) (fun a => (hx a).1) (fun a => (hx a).2)).1
    change 0 ≤ gap xs
    change g xs Finset.univ ≥ g xs ∅ + ∑ i, (g xs {i}-g xs ∅) at hh
    change 0 ≤ g xs Finset.univ-g xs ∅-∑ i, (g xs {i}-g xs ∅)
    linarith
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; simp [i,j] at hh
  let E : Set (Fin d → ℝ × ℝ) := {xs | (xs i).1 < (xs i).2 ∧ (xs j).1 < (xs j).2 ∧
    ∀ a, a ≠ i → a ≠ j → 0 < (xs a).1}
  have hE : 0 < μ E := size_bias_strict_product_event d hd π hs hp
  have hsub : ∀ᵐ xs ∂μ, xs ∈ E → xs ∈ Function.support gap := by
    filter_upwards [hgood] with xs hx hxs
    have hh := (hardcore_log_product_supermodular_gap θ hθ.le (fun a => (xs a).1)
      (fun a => (xs a).2) (fun a => (hx a).1) (fun a => (hx a).2)).2
      hθ i j hij hxs.1 hxs.2.1 hxs.2.2
    change gap xs ≠ 0
    change g xs Finset.univ > g xs ∅ + ∑ i, (g xs {i}-g xs ∅) at hh
    change g xs Finset.univ-g xs ∅-∑ i, (g xs {i}-g xs ∅) ≠ 0
    linarith
  have hsupport : 0 < μ (Function.support gap) := lt_of_lt_of_le hE (measure_mono_ae hsub)
  exact (integral_pos_iff_support_of_nonneg_ae hnonneg hI).2 hsupport
