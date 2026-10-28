-- Prove2me | solution 1 for SphereGRF.Spectral.weight_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:36:45.731209+00:00
-- url     : https://prove2.me/submissions/a6e476af-5f91-458a-b22f-94859fa987f0

import Mathlib
import Definitions.Def_SphereGRF_Spectral_FourierLegendre

namespace Aux_SGRF_WE

lemma Gbounds (n : ℕ) (θ L : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hL : L = 0 ∨ 1 ≤ L) :
    1 / 2 * (1 + L ^ (2 * ((n : ℝ) + θ))) ≤
        (1 + L ^ (2 * (n : ℝ))) ^ (1 - θ) * (1 + L ^ (2 * ((n : ℝ) + 1))) ^ θ ∧
      (1 + L ^ (2 * (n : ℝ))) ^ (1 - θ) * (1 + L ^ (2 * ((n : ℝ) + 1))) ^ θ ≤
        2 * (1 + L ^ (2 * ((n : ℝ) + θ))) := by
  have hL0 : 0 ≤ L := by rcases hL with h | h <;> linarith
  obtain ⟨x, hx⟩ : ∃ x, x = L ^ (2 * (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = L ^ (2 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = L ^ (2 * ((n : ℝ) + θ)) := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hz]
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.rpow_nonneg hL0 _
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.rpow_nonneg hL0 _
  have hz0 : 0 ≤ z := by rw [hz]; exact Real.rpow_nonneg hL0 _
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hGA : 1 ≤ (1 + x) ^ (1 - θ) := Real.one_le_rpow (by linarith) h1θ
  have hGB : 1 ≤ (1 + y) ^ θ := Real.one_le_rpow (by linarith) hθ₀.le
  have hG1 : 1 ≤ (1 + x) ^ (1 - θ) * (1 + y) ^ θ := one_le_mul_of_one_le_of_one_le hGA hGB
  have h22 : (2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ θ = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  rcases hL with h | h
  · have hx1 : x ≤ 1 := by rw [hx, h]; exact Real.zero_rpow_le_one _
    have hy1 : y ≤ 1 := by rw [hy, h]; exact Real.zero_rpow_le_one _
    have hz1 : z ≤ 1 := by rw [hz, h]; exact Real.zero_rpow_le_one _
    have hu : (1 + x) ^ (1 - θ) * (1 + y) ^ θ ≤ (2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ θ :=
      mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) h1θ)
        (Real.rpow_le_rpow (by linarith) (by linarith) hθ₀.le)
        (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
    constructor
    · linarith
    · linarith
  · have hLp : 0 < L := by linarith
    have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_rpow h (by positivity)
    have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_rpow h (by positivity)
    have hzxy : z = x ^ (1 - θ) * y ^ θ := by
      rw [hz, hx, hy, ← Real.rpow_mul hL0, ← Real.rpow_mul hL0, ← Real.rpow_add hLp]
      congr 1
      ring
    have hlow : x ^ (1 - θ) * y ^ θ ≤ (1 + x) ^ (1 - θ) * (1 + y) ^ θ :=
      mul_le_mul (Real.rpow_le_rpow hx0 (by linarith) h1θ)
        (Real.rpow_le_rpow hy0 (by linarith) hθ₀.le)
        (Real.rpow_nonneg hy0 _) (Real.rpow_nonneg (by linarith) _)
    have hup : (1 + x) ^ (1 - θ) * (1 + y) ^ θ ≤ (2 * x) ^ (1 - θ) * (2 * y) ^ θ :=
      mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) h1θ)
        (Real.rpow_le_rpow (by linarith) (by linarith) hθ₀.le)
        (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    have h2z : (2 * x) ^ (1 - θ) * (2 * y) ^ θ = 2 * z := by
      rw [Real.mul_rpow (by norm_num) hx0, Real.mul_rpow (by norm_num) hy0, hzxy]
      calc (2 : ℝ) ^ (1 - θ) * x ^ (1 - θ) * ((2 : ℝ) ^ θ * y ^ θ)
          = ((2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ θ) * (x ^ (1 - θ) * y ^ θ) := by ring
        _ = 2 * (x ^ (1 - θ) * y ^ θ) := by rw [h22]
    rw [← hzxy] at hlow
    constructor
    · linarith
    · linarith

lemma core (n : ℕ) (θ L : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hL : L = 0 ∨ 1 ≤ L) :
    1 / 2 * ((2 * L + 1) / 2 * (1 + L ^ (2 * ((n : ℝ) + θ)))) ≤
        ((2 * L + 1) / 2 * (1 + L ^ (2 * (n : ℝ)))) ^ (1 - θ) *
          ((2 * L + 1) / 2 * (1 + L ^ (2 * ((n : ℝ) + 1)))) ^ θ ∧
      ((2 * L + 1) / 2 * (1 + L ^ (2 * (n : ℝ)))) ^ (1 - θ) *
          ((2 * L + 1) / 2 * (1 + L ^ (2 * ((n : ℝ) + 1)))) ^ θ ≤
        2 * ((2 * L + 1) / 2 * (1 + L ^ (2 * ((n : ℝ) + θ)))) := by
  have hL0 : 0 ≤ L := by rcases hL with h | h <;> linarith
  obtain ⟨hlo, hhi⟩ := Gbounds n θ L hθ₀ hθ₁ hL
  obtain ⟨a, ha⟩ : ∃ a, a = (2 * L + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 1 + L ^ (2 * (n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 1 + L ^ (2 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 1 + L ^ (2 * ((n : ℝ) + θ)) := ⟨_, rfl⟩
  rw [← ha, ← hA, ← hB, ← hC]
  rw [← hA, ← hB, ← hC] at hlo hhi
  have ha0 : 0 < a := by rw [ha]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; linarith [Real.rpow_nonneg hL0 (2 * (n : ℝ))]
  have hB0 : 0 ≤ B := by rw [hB]; linarith [Real.rpow_nonneg hL0 (2 * ((n : ℝ) + 1))]
  have haa : a ^ (1 - θ) * a ^ θ = a := by
    rw [← Real.rpow_add ha0]
    simp
  have hprod : (a * A) ^ (1 - θ) * (a * B) ^ θ = a * (A ^ (1 - θ) * B ^ θ) := by
    rw [Real.mul_rpow ha0.le hA0, Real.mul_rpow ha0.le hB0]
    calc a ^ (1 - θ) * A ^ (1 - θ) * (a ^ θ * B ^ θ)
        = (a ^ (1 - θ) * a ^ θ) * (A ^ (1 - θ) * B ^ θ) := by ring
      _ = a * (A ^ (1 - θ) * B ^ θ) := by rw [haa]
  rw [hprod]
  have h1 := mul_le_mul_of_nonneg_left hlo ha0.le
  have h2 := mul_le_mul_of_nonneg_left hhi ha0.le
  constructor
  · linarith
  · linarith

end Aux_SGRF_WE

open SphereGRF.Spectral Aux_SGRF_WE in
theorem solution (n : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ,
      c₁ * specWeight ((n : ℝ) + θ) ℓ ≤
        specWeight (n : ℝ) ℓ ^ (1 - θ) * specWeight ((n : ℝ) + 1) ℓ ^ θ ∧
      specWeight (n : ℝ) ℓ ^ (1 - θ) * specWeight ((n : ℝ) + 1) ℓ ^ θ ≤
        c₂ * specWeight ((n : ℝ) + θ) ℓ := by
  refine ⟨1 / 2, 2, by norm_num, by norm_num, fun ℓ => ?_⟩
  unfold specWeight
  have hL : (ℓ : ℝ) = 0 ∨ 1 ≤ (ℓ : ℝ) := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · left; simp [h]
    · right; exact Nat.one_le_cast.mpr h
  exact core n θ (ℓ : ℝ) hθ₀ hθ₁ hL
