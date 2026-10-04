-- Prove2me | solution 1 for TeschlODE.Horseshoe.symDistZ_agree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:21:45.122137+00:00
-- url     : https://prove2.me/submissions/bf6736a8-2e93-4a36-bf80-5682bf0345a6

import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_symDistZ

set_option autoImplicit false

namespace C5A32A60

lemma one_le_abs_sub {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith

lemma abs_sub_le_N {N : ℕ} (a b : Fin N) : |((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)| ≤ (N : ℝ) - 1 := by
  have ha' : (a : ℕ) + 1 ≤ N := a.isLt
  have hb' : (b : ℕ) + 1 ≤ N := b.isLt
  have ha : ((a : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb : ((b : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have h0a := Nat.cast_nonneg (α := ℝ) (a : ℕ)
  have h0b := Nat.cast_nonneg (α := ℝ) (b : ℕ)
  rw [abs_sub_le_iff]; constructor <;> linarith

end C5A32A60

open TeschlODE.Horseshoe in
theorem solution (N : ℕ) (hN : 2 ≤ N) (x y : ℤ → Fin N) (n : ℕ) :
    ((∀ j : ℤ, |j| ≤ n → x j = y j) → symDistZ N x y ≤ 1 / (N : ℝ) ^ n) ∧
      ((∃ j : ℤ, |j| ≤ n ∧ x j ≠ y j) → 1 / (2 * (N : ℝ) ^ n) ≤ symDistZ N x y) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set r : ℝ := 1 / (N : ℝ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hNpos]; linarith
  set f : ℕ → ℝ := fun k =>
    (|((x k : ℕ) : ℝ) - ((y k : ℕ) : ℝ)| + |((x (-(k : ℤ)) : ℕ) : ℝ) - ((y (-(k : ℤ)) : ℕ) : ℝ)|) /
      (N : ℝ) ^ k with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by rw [hf]; positivity
  have hfb : ∀ k, f k ≤ (2 * ((N : ℝ) - 1)) * r ^ k := by
    intro k
    rw [hf, hrdef]
    simp only
    rw [div_pow, one_pow, ← div_eq_mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := C5A32A60.abs_sub_le_N (x k) (y k)
    have := C5A32A60.abs_sub_le_N (x (-(k : ℤ))) (y (-(k : ℤ)))
    linarith
  have hgs : Summable (fun k : ℕ => (2 * ((N : ℝ) - 1)) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hfs : Summable f := Summable.of_nonneg_of_le hfnn hfb hgs
  have hd : symDistZ N x y = 1 / 2 * ∑' k, f k := rfl
  constructor
  · intro hag
    have hzero : ∀ k, k < n + 1 → f k = 0 := by
      intro k hk
      have hkn : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : k ≤ n)
      have h1 : x k = y k := hag k (by rw [abs_of_nonneg (by positivity)]; exact hkn)
      have h2 : x (-(k : ℤ)) = y (-(k : ℤ)) :=
        hag _ (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hkn)
      rw [hf]
      simp only
      rw [h1, h2]
      simp
    have hsplit := hfs.sum_add_tsum_nat_add (n + 1)
    have hsum0 : ∑ i ∈ Finset.range (n + 1), f i = 0 :=
      Finset.sum_eq_zero (fun i hi => hzero i (Finset.mem_range.1 hi))
    rw [hsum0, zero_add] at hsplit
    have htail : ∀ i, f (i + (n + 1)) ≤ ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i := by
      intro i
      calc f (i + (n + 1)) ≤ (2 * ((N : ℝ) - 1)) * r ^ (i + (n + 1)) := hfb _
        _ = ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i := by rw [pow_add]; ring
    have hts : Summable (fun i => f (i + (n + 1))) := (summable_nat_add_iff (n + 1)).2 hfs
    have hgs2 : Summable (fun i : ℕ => ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    have hle := Summable.tsum_le_tsum htail hts hgs2
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
    have key : (2 * ((N : ℝ) - 1)) * r ^ (n + 1) * (1 - r)⁻¹ = 2 * (1 / (N : ℝ) ^ n) := by
      have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
      have hNne : (N : ℝ) ≠ 0 := by linarith
      have hpow : (N : ℝ) ^ n ≠ 0 := pow_ne_zero _ hNne
      rw [hrdef, one_div, inv_pow, pow_succ]
      field_simp
    rw [hd, ← hsplit]
    linarith
  · rintro ⟨j, hj, hne⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · have hk : k ≤ n := by
        rw [abs_of_nonneg (by positivity)] at hj; exact_mod_cast hj
      have hfk : 1 / (N : ℝ) ^ k ≤ f k := by
        rw [hf]
        simp only
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := C5A32A60.one_le_abs_sub (fun h => hne (Fin.ext h))
        have := abs_nonneg (((x (-(k : ℤ)) : ℕ) : ℝ) - ((y (-(k : ℤ)) : ℕ) : ℝ))
        linarith
      have h1 : f k ≤ ∑' i, f i := hfs.le_tsum k (fun i _ => hfnn i)
      have h2 : 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ k :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) hk)
      rw [hd, ← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    · have hk : k ≤ n := by
        rw [abs_neg, abs_of_nonneg (by positivity)] at hj; exact_mod_cast hj
      have hfk : 1 / (N : ℝ) ^ k ≤ f k := by
        rw [hf]
        simp only
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := C5A32A60.one_le_abs_sub (fun h => hne (Fin.ext h))
        have := abs_nonneg (((x (k : ℤ) : ℕ) : ℝ) - ((y (k : ℤ) : ℕ) : ℝ))
        linarith
      have h1 : f k ≤ ∑' i, f i := hfs.le_tsum k (fun i _ => hfnn i)
      have h2 : 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ k :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) hk)
      rw [hd, ← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
