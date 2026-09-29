-- Prove2me | solution 1 for QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/33491486-3397-5b60-9bcc-f6836fd6e0a0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero

set_option autoImplicit false

namespace TernChi

variable {K : Type} [Field K] (a b : K)

theorem quat_of_tern (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0)
    (x₀ x₁ x₂ x₃ : K) (hq : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by

  have hN : x₀ ^ 2 - a * x₁ ^ 2 = b * (x₂ ^ 2 - a * x₃ ^ 2) := by linear_combination hq
  by_cases hD : x₂ ^ 2 - a * x₃ ^ 2 = 0
  ·
    have hN0 : x₀ ^ 2 - a * x₁ ^ 2 = 0 := by rw [hN, hD, mul_zero]
    by_cases hx3 : x₃ = 0
    ·
      have hx2 : x₂ = 0 := by
        subst hx3
        have : x₂ ^ 2 = 0 := by simpa using hD
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      obtain ⟨h0, h1, -⟩ := h x₀ x₁ 0 (by rw [hN0]; ring)
      exact ⟨h0, h1, hx2, hx3⟩
    ·
      exfalso
      obtain ⟨-, h3, -⟩ := h x₂ x₃ 0 (by linear_combination hD)
      exact hx3 h3
  ·
    exfalso
    set D := x₂ ^ 2 - a * x₃ ^ 2 with hDdef
    obtain ⟨-, -, h1⟩ := h ((x₀ * x₂ - a * x₁ * x₃) / D) ((x₁ * x₂ - x₀ * x₃) / D) 1 (by
      field_simp

      have key : (x₀ * x₂ - a * x₁ * x₃) ^ 2 - a * (x₁ * x₂ - x₀ * x₃) ^ 2 =
          (x₀ ^ 2 - a * x₁ ^ 2) * (x₂ ^ 2 - a * x₃ ^ 2) := by ring
      rw [hN] at key
      linear_combination key)
    exact one_ne_zero h1

theorem tern_of_quat
    (h : ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0)
    (z x y : K) (ht : z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) : z = 0 ∧ x = 0 ∧ y = 0 := by
  obtain ⟨h0, h1, h2, -⟩ := h z x y 0 (by linear_combination ht)
  exact ⟨h0, h1, h2⟩

theorem main (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  ⟨fun h z x y ht => tern_of_quat a b h z x y ht, fun h x₀ x₁ x₂ x₃ hq => quat_of_tern a b ha hb h x₀ x₁ x₂ x₃ hq⟩

end TernChi

theorem solution
    (K : Type) [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  TernChi.main a b ha hb

end S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
end P2MW
export P2MW.S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero (solution)
