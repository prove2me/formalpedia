-- Prove2me | solution 1 for SmallRatio.dedekind_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:04.660369+00:00
-- url     : https://prove2.me/submissions/f6305a7c-af9f-4513-b6b7-4e748f43fdfe

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
public import Theorems.Thm_SmallRatio_sum_mul_mod_perm
public import Theorems.Thm_SmallRatio_dedekindSum_eq_Asum
public import Theorems.Thm_SmallRatio_sum_odd
public import Theorems.Thm_SmallRatio_sum_floor_sq
public import Theorems.Thm_SmallRatio_sum_floor
public import Theorems.Thm_SmallRatio_sum_sq_range

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h =
      ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by
  rw [dedekindSum_eq_Asum h k hk hc, dedekindSum_eq_Asum k h hh (Nat.Coprime.symm hc)]
  -- the unknowns
  set S2k : ℚ := ∑ r ∈ range k, (r : ℚ) ^ 2
  set S2h : ℚ := ∑ j ∈ range h, (j : ℚ) ^ 2
  set F : ℚ := ∑ r ∈ range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ)
  set G : ℚ := ∑ j ∈ range h, (j : ℚ) * ((k * j / h : ℕ) : ℚ)
  set Sf2 : ℚ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) ^ 2
  set Sg : ℚ := ∑ j ∈ range h, ((k * j / h : ℕ) : ℚ)
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  -- `hr mod k = hr - k ⌊hr/k⌋`
  have hmodk : ∀ r : ℕ, ((h * r % k : ℕ) : ℚ) = (h : ℚ) * r - k * ((h * r / k : ℕ) : ℚ) := by
    intro r
    have := Nat.mod_add_div (h * r) k
    have : ((h * r % k : ℕ) : ℚ) + k * ((h * r / k : ℕ) : ℚ) = (h : ℚ) * r := by exact_mod_cast this
    linarith
  have hmodh : ∀ j : ℕ, ((k * j % h : ℕ) : ℚ) = (k : ℚ) * j - h * ((k * j / h : ℕ) : ℚ) := by
    intro j
    have := Nat.mod_add_div (k * j) h
    have : ((k * j % h : ℕ) : ℚ) + h * ((k * j / h : ℕ) : ℚ) = (k : ℚ) * j := by exact_mod_cast this
    linarith
  have e1 : (Asum h k : ℚ) = h * S2k - k * F := by
    unfold Asum; push_cast
    simp_rw [hmodk]
    simp only [S2k, F, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro r _; ring
  have e2 : (Asum k h : ℚ) = k * S2h - h * G := by
    unfold Asum; push_cast
    simp_rw [hmodh]
    simp only [S2h, G, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro r _; ring
  -- `∑ (hr mod k)² = ∑ r²`
  have e3 : (h : ℚ) ^ 2 * S2k - 2 * h * k * F + k ^ 2 * Sf2 = S2k := by
    have hp := sum_mul_mod_perm h k hk hc (fun r => ((r : ℕ) : ℚ) ^ 2)
    simp_rw [hmodk] at hp
    rw [show (h : ℚ) ^ 2 * S2k - 2 * h * k * F + k ^ 2 * Sf2 =
        ∑ x ∈ range k, ((h : ℚ) * x - k * ((h * x / k : ℕ) : ℚ)) ^ 2 from ?_]
    · exact hp
    · simp only [S2k, F, Sf2, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro r _; ring
  -- lattice points
  have e4 : Sf2 = ((k : ℚ) - 1) * ((h : ℚ) - 1) ^ 2 - 2 * G + Sg := by
    have hl := sum_floor_sq h k hh hk hc
    have hl' : Sf2 = ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) * ((k : ℚ) - 1 - ((k * j / h : ℕ) : ℚ)) := by
      have := congrArg (Int.cast : ℤ → ℚ) hl
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_ofNat, Int.cast_one] at this
      simp only [Sf2]; exact this
    rw [hl']
    have hshift : ∀ f : ℕ → ℚ, f 0 = 0 → ∑ j ∈ Ico 1 h, f j = ∑ j ∈ range h, f j := by
      intro f hf0
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ h)]
      simp [hf0]
    have hodd : ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) = ((h : ℚ) - 1) ^ 2 := by
      obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
      have := sum_odd m
      have : ∑ j ∈ Ico 1 (m + 1), (2 * (j : ℚ) - 1) = (m : ℚ) ^ 2 := by exact_mod_cast this
      rw [this]; push_cast; ring
    have hsplit : ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1) * ((k : ℚ) - 1 - ((k * j / h : ℕ) : ℚ)) =
        ((k : ℚ) - 1) * ∑ j ∈ Ico 1 h, (2 * (j : ℚ) - 1)
          - 2 * ∑ j ∈ Ico 1 h, (j : ℚ) * ((k * j / h : ℕ) : ℚ)
          + ∑ j ∈ Ico 1 h, ((k * j / h : ℕ) : ℚ) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro j _; ring
    rw [hsplit, hodd, hshift (fun j => (j : ℚ) * ((k * j / h : ℕ) : ℚ)) (by simp),
      hshift (fun j => ((k * j / h : ℕ) : ℚ)) (by simp)]
  have e5 : 2 * Sg = ((h : ℚ) - 1) * ((k : ℚ) - 1) := by
    have := congrArg (Int.cast : ℤ → ℚ) (sum_floor h k hh hc)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat, Int.cast_one] at this
    simp only [Sg]; exact this
  have e6 : 6 * S2k = ((k : ℚ) - 1) * k * (2 * k - 1) := by
    simp only [S2k]; exact sum_sq_range k
  have e7 : 6 * S2h = ((h : ℚ) - 1) * h * (2 * h - 1) := by
    simp only [S2h]; exact sum_sq_range h
  have key : 12 * (h : ℚ) ^ 2 * (h * S2k - k * F) + 12 * (k : ℚ) ^ 2 * (k * S2h - h * G) =
      (h : ℚ) ^ 3 * k + h * k ^ 3 + h * k + 3 * h ^ 2 * k ^ 2 * (h + k - 3) := by
    linear_combination 6 * (h : ℚ) * e3 - 6 * (h : ℚ) * k ^ 2 * e4 - 3 * (h : ℚ) * k ^ 2 * e5
      + (h : ℚ) * (h ^ 2 + 1) * e6 + 2 * (k : ℚ) ^ 3 * e7
  rw [e1, e2]
  field_simp
  linear_combination 4 * key
end SmallRatio
