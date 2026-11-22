-- Prove2me | solution 1 for Pseudorandom.exp_step_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:35.517681+00:00
-- url     : https://prove2.me/submissions/1e03f48f-1e37-4206-92ae-5afafdd46df2

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman
public import Theorems.Thm_Pseudorandom_exp_le_one_add_add_sq_div


set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
theorem _root_.solution (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (Δ : α → ℝ)
    (hmean : ∑ a, p a * Δ a = 0) (C θ : ℝ) (hθ : 0 ≤ θ) (hθC : θ * C < 1)
    (hΔ : ∀ a, p a ≠ 0 → |Δ a| ≤ C) :
    ∑ a, p a * Real.exp (θ * Δ a) ≤
      Real.exp (θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a|) := by
  have hK : 0 < 2 * (1 - θ * C) := by linarith
  have hpt : ∀ a, p a * Real.exp (θ * Δ a) ≤
      p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    apply mul_le_mul_of_nonneg_left _ (hp0 a)
    have hC := hΔ a hpa
    have h1 := exp_le_one_add_add_sq_div (θ * Δ a) (θ * C)
      (by rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hC hθ) hθC
    have h2 : (θ * Δ a) ^ 2 / (2 * (1 - θ * C)) ≤ θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a| := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hK.le
      have : Δ a ^ 2 ≤ C * |Δ a| := by
        rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)
      calc (θ * Δ a) ^ 2 = θ ^ 2 * Δ a ^ 2 := by ring
        _ ≤ θ ^ 2 * (C * |Δ a|) := mul_le_mul_of_nonneg_left this (sq_nonneg θ)
        _ = θ ^ 2 * C * |Δ a| := by ring
    linarith
  calc ∑ a, p a * Real.exp (θ * Δ a)
      ≤ ∑ a, p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) :=
        sum_le_sum fun a _ => hpt a
    _ = ∑ a, p a + θ * ∑ a, p a * Δ a +
          θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by
        rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun a _ => by ring
    _ = 1 + θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by rw [hp1, hmean]; ring
    _ ≤ _ := by linarith [Real.add_one_le_exp (θ ^ 2 * C / (2 * (1 - θ * C)) *
          ∑ a, p a * |Δ a|)]
end Pseudorandom
