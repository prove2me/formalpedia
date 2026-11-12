-- Prove2me | solution 1 for SuperRamanujan227.Main.claim_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:15:45.265139+00:00
-- url     : https://prove2.me/submissions/a9e95ccf-ce6d-4b85-be22-f9b889970e17

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Jacobi

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.C55
open SuperRamanujan227.Main

lemma gbinom_nat (m k : ℕ) : gbinom (m : ℝ) k = (m.choose k : ℝ) := by
  unfold gbinom
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- the coefficient identity -/
lemma coef_id (n a t : ℕ) (ht : t ≤ n) :
    ((n + 2 * a).choose (a + t) : ℝ) * (((n + a).descFactorial (n + a - t) : ℕ) : ℝ) *
        (((n + a).descFactorial (a + t) : ℕ) : ℝ)
      = ((n + 2 * a).factorial : ℝ) * ((n + a).choose t : ℝ) * ((n + a).choose (n - t) : ℝ) := by
  have e1 : (n + 2 * a) - (a + t) = n + a - t := by omega
  have h1 := Nat.cast_choose ℝ (show a + t ≤ n + 2 * a by omega)
  have h2 := Nat.cast_choose ℝ (show t ≤ n + a by omega)
  have h3 := Nat.cast_choose ℝ (show n - t ≤ n + a by omega)
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have h4 := Nat.cast_choose ℝ (show n + a - t ≤ n + a by omega)
  have h5 := Nat.cast_choose ℝ (show a + t ≤ n + a by omega)
  rw [e1] at h1
  have e2 : n + a - (n - t) = a + t := by omega
  have e3 : n + a - t = n + a - t := rfl
  have e4 : n + a - (n + a - t) = t := by omega
  have e5 : n + a - (a + t) = n - t := by omega
  rw [e2] at h3
  rw [e4] at h4
  rw [e5] at h5
  push_cast
  rw [h1, h2, h3, h4, h5]
  have : ∀ x : ℕ, (x.factorial : ℝ) ≠ 0 := fun x => by positivity
  have f1 := this (a + t); have f2 := this (n + a - t); have f3 := this t; have f4 := this (n - t)
  have f5 := this (n + a)
  field_simp


lemma leibniz (n a : ℕ) :
    derivative^[n + 2 * a] ((X ^ 2 - 1 : ℝ[X]) ^ (n + a)) =
      ∑ t ∈ Finset.range (n + 1),
        ((n + 2 * a).choose (a + t) * (n + a).descFactorial (n + a - t) *
            (n + a).descFactorial (a + t) : ℕ) •
          ((X - 1 : ℝ[X]) ^ t * (X + 1) ^ (n - t)) := by
  have hf : (X ^ 2 - 1 : ℝ[X]) ^ (n + a) = (X - C 1) ^ (n + a) * (X + C 1) ^ (n + a) := by
    rw [← mul_pow]; congr 1; simp only [map_one]; ring
  rw [hf, iterate_derivative_mul]
  simp only [iterate_derivative_X_sub_pow, iterate_derivative_X_add_pow]
  have hsub : ∀ s ∈ Finset.range (n + 2 * a).succ, s ∉ Finset.Ico a (a + n + 1) →
      (((n + 2 * a).choose s) • (((n + a).descFactorial (n + 2 * a - s) • (X - C (1:ℝ)) ^ (n + a - (n + 2 * a - s))) *
        ((n + a).descFactorial s • (X + C (1:ℝ)) ^ (n + a - s)))) = 0 := by
    intro s _ hs
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hs
    rcases hs with h | h
    · have : n + a < n + 2 * a - s := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr this]; simp
    · have : n + a < s := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr this]; simp
  rw [← Finset.sum_subset (s₁ := Finset.Ico a (a + n + 1)) _ hsub]
  · rw [Finset.sum_Ico_eq_sum_range]
    have e : a + n + 1 - a = n + 1 := by omega
    rw [e]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have e1 : n + 2 * a - (a + t) = n + a - t := by omega
    have e2 : n + a - (n + a - t) = t := by omega
    have e3 : n + a - (a + t) = n - t := by omega
    rw [e1, e2, e3]
    simp only [map_one, nsmul_eq_mul]
    push_cast
    ring
  · intro s hs
    simp only [Finset.mem_Ico, Finset.mem_range] at hs ⊢
    omega

lemma main (n a : ℕ) :
    derivative^[n + 2 * a] ((X ^ 2 - 1 : ℝ[X]) ^ (n + a)) =
      C (((n + 2 * a).factorial : ℝ) * 2 ^ n) * SuperRamanujan227.Main.jacobiSym (a : ℝ) n := by
  rw [leibniz]
  unfold SuperRamanujan227.Main.jacobiSym SuperRamanujan227.Main.jacobi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ n := by have := Finset.mem_range.mp ht; omega
  have hcast : (n : ℝ) + (a : ℝ) = ((n + a : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, gbinom_nat, gbinom_nat]
  have hN := coef_id n a t ht'
  rw [nsmul_eq_mul, ← C_eq_natCast]
  have hh : (C (1 / 2 : ℝ)) ^ t * (C (1 / 2 : ℝ)) ^ (n - t) * (C (2 : ℝ)) ^ n = 1 := by
    rw [← pow_add, show t + (n - t) = n by omega, ← mul_pow, ← C_mul]
    norm_num
  have hN' : (((n + 2 * a).choose (a + t) * (n + a).descFactorial (n + a - t) *
            (n + a).descFactorial (a + t) : ℕ) : ℝ) =
      ((n + 2 * a).factorial : ℝ) * ((n + a).choose t : ℝ) * ((n + a).choose (n - t) : ℝ) := by
    push_cast; exact hN
  rw [hN']
  simp only [map_mul, map_pow, C_eq_natCast, mul_pow]
  linear_combination
    (-(((n + 2 * a).factorial : ℝ[X]) * ((n + a).choose t : ℝ[X]) * ((n + a).choose (n - t) : ℝ[X]) *
      ((X - 1 : ℝ[X]) ^ t * (X + 1) ^ (n - t)))) * hh

end SuperRamanujan227.Dev.C55

namespace SuperRamanujan227.Main
open SuperRamanujan227.Dev.C55

theorem chk_claim_5_5 (n d : ℕ) (hn : 2 ≤ n) (hd : 3 ≤ d) (hnd : Even (n * d)) :
    ∃ c : ℝ, c ≠ 0 ∧ Q n d = C c * jacobiSym ((n : ℝ) * ((d : ℝ) - 2) / 2) n := by
  obtain ⟨r, hr⟩ := hnd
  have hnd2 : n * d / 2 = r := by omega
  have hge : n ≤ r := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, r = n + a := ⟨r - n, by omega⟩
  have hk : n * (d - 1) = n + 2 * a := by
    have : n * (d - 1) = n * d - n := by rw [Nat.mul_sub, Nat.mul_one]
    omega
  have hpar : (n : ℝ) * ((d : ℝ) - 2) / 2 = (a : ℝ) := by
    have h1 : (n : ℝ) * d = 2 * (n + a) := by exact_mod_cast (by omega : n * d = 2 * (n + a))
    linarith
  refine ⟨((n + 2 * a).factorial : ℝ) * 2 ^ n, by positivity, ?_⟩
  rw [hpar]
  unfold Q
  rw [hnd2, hk, ha]
  exact main n a

end SuperRamanujan227.Main
end

theorem solution : type_of% @SuperRamanujan227.Main.chk_claim_5_5 := @SuperRamanujan227.Main.chk_claim_5_5
