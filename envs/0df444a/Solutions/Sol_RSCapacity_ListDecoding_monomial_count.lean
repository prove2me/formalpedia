-- Prove2me | solution 1 for RSCapacity.ListDecoding.monomial_count
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:02:59.709655+00:00
-- url     : https://prove2.me/submissions/944b8a5d-323b-477d-bee0-26375a4daf64

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Counting

set_option autoImplicit false

open scoped BigOperators

open RSCapacity.ListDecoding

private lemma card_eq_sum (k D : ℕ) :
    (bivariateMonomials k D).card = ∑ b ∈ Finset.range D, (D - k * b) := by
  unfold bivariateMonomials
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.card_filter]
  have : (Finset.range D).filter (fun a => a + k * b < D) = Finset.range (D - k * b) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

private lemma sum_real (k D : ℕ) (m : ℕ) :
    ∑ b ∈ Finset.range m, ((D : ℝ) - k * b) = m * D - k * m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem solution (k D : ℕ) (hk : 0 < k) (hD : 0 < D) :
    (D : ℝ) * (D + k) / (2 * k) ≤ (bivariateMonomials k D).card ∧
    ((bivariateMonomials k D).card : ℝ) ≤
      (D : ℝ) * (D + k) / (2 * k) + (k : ℝ) / 8 := by
  set m := (D + k - 1) / k with hm
  have hdm := Nat.div_add_mod (D + k - 1) k
  have hmod := Nat.mod_lt (D + k - 1) hk
  rw [← hm] at hdm
  have hkm1 : k * m ≤ D + k - 1 := by omega
  have hkm2 : D ≤ k * m := by omega
  have hmD : m ≤ D := Nat.div_le_of_le_mul (by
    obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, D = b + 1 := ⟨D - 1, by omega⟩
    have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    omega)
  have hsum : ∑ b ∈ Finset.range D, (D - k * b) = ∑ b ∈ Finset.range m, (D - k * b) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hmD)
    intro b _ hb
    rw [Finset.mem_range, not_lt] at hb
    have : k * m ≤ k * b := Nat.mul_le_mul_left k hb
    omega
  have hcard : ((bivariateMonomials k D).card : ℝ) = m * D - k * m * (m - 1) / 2 := by
    rw [card_eq_sum, hsum, Nat.cast_sum, ← sum_real]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    have : k * (b + 1) ≤ k * m := Nat.mul_le_mul_left k hb
    rw [Nat.cast_sub (by rw [Nat.mul_add] at this; omega)]
    push_cast; ring
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs1 : (D : ℝ) ≤ k * m := by exact_mod_cast hkm2
  have hs2 : (k : ℝ) * m ≤ D + k - 1 := by
    have : k * m + 1 ≤ D + k := by omega
    have : ((k * m + 1 : ℕ) : ℝ) ≤ ((D + k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  set s : ℝ := k * m - D with hs
  have hD' : (D : ℝ) = k * m - s := by rw [hs]; ring
  have key : (bivariateMonomials k D).card * (2 * k) - (D : ℝ) * (D + k) = s * (k - s) := by
    rw [hcard, hD']; ring
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * s - k)]
