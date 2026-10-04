-- Prove2me | solution 1 for TeschlODE.IntervalMaps.symDist_agree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:54:39.243087+00:00
-- url     : https://prove2.me/submissions/649b261d-6aa5-49a7-8834-0fc0c6c5c64d

import Mathlib
import Definitions.Def_TeschlODE_Shared_symDist

set_option autoImplicit false

theorem a10058ab_term_bound (N : ℕ) (x y : ℕ → Fin N) (k : ℕ) :
    |((x k : ℕ) : ℝ) - ((y k : ℕ) : ℝ)| ≤ (N : ℝ) - 1 := by
  have hx : ((x k : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (x k).isLt
  have hy : ((y k : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (y k).isLt
  have hx0 : (0 : ℝ) ≤ ((x k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ ((y k : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem a10058ab_summable (N : ℕ) (hN : 2 ≤ N) (x y : ℕ → Fin N) :
    Summable (fun k : ℕ => |((x k : ℕ) : ℝ) - ((y k : ℕ) : ℝ)| / (N : ℝ) ^ k) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  have hr1 : (N : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg : Summable (fun k : ℕ => ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
  · exact div_nonneg (abs_nonneg _) (pow_nonneg hNpos.le _)
  · rw [inv_pow, ← div_eq_mul_inv]
    gcongr
    exact a10058ab_term_bound N x y k

open TeschlODE.Shared in
theorem solution (N : ℕ) (hN : 2 ≤ N) (x y : ℕ → Fin N) (n : ℕ) :
    ((∀ j, j ≤ n → x j = y j) → TeschlODE.Shared.symDist N x y ≤ 1 / (N : ℝ) ^ n) ∧
      ((∃ j, j ≤ n ∧ x j ≠ y j) → 1 / (N : ℝ) ^ n ≤ TeschlODE.Shared.symDist N x y) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  have hr1 : (N : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs := a10058ab_summable N hN x y
  set f : ℕ → ℝ := fun k => |((x k : ℕ) : ℝ) - ((y k : ℕ) : ℝ)| / (N : ℝ) ^ k with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => div_nonneg (abs_nonneg _) (pow_nonneg hNpos.le _)
  have hd : symDist N x y = ∑' k, f k := rfl
  constructor
  · intro hag
    rw [hd, ← hs.sum_add_tsum_nat_add (n + 1)]
    have hzero : ∑ i ∈ Finset.range (n + 1), f i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp [hf, hag i hi']
    rw [hzero, zero_add]
    have hg : Summable (fun i : ℕ => ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ (n + 1) * ((N : ℝ)⁻¹) ^ i) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    have hle : ∀ i, f (i + (n + 1)) ≤ ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ (n + 1) * ((N : ℝ)⁻¹) ^ i := by
      intro i
      have h1 : f (i + (n + 1)) ≤ ((N : ℝ) - 1) / (N : ℝ) ^ (i + (n + 1)) := by
        simp only [hf]
        gcongr
        exact a10058ab_term_bound N x y _
      calc f (i + (n + 1)) ≤ ((N : ℝ) - 1) / (N : ℝ) ^ (i + (n + 1)) := h1
        _ = ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ (n + 1) * ((N : ℝ)⁻¹) ^ i := by
          rw [div_eq_mul_inv, ← inv_pow, pow_add]; ring
    have hsub : Summable (fun i => f (i + (n + 1))) := (summable_nat_add_iff (n + 1)).mpr hs
    calc ∑' i, f (i + (n + 1))
        ≤ ∑' i, ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ (n + 1) * ((N : ℝ)⁻¹) ^ i :=
          hsub.tsum_le_tsum hle hg
      _ = ((N : ℝ) - 1) * ((N : ℝ)⁻¹) ^ (n + 1) * (1 - (N : ℝ)⁻¹)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ = 1 / (N : ℝ) ^ n := by
          have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
          have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
          have h1r : 1 - (N : ℝ)⁻¹ = ((N : ℝ) - 1) / (N : ℝ) := by field_simp
          rw [h1r, inv_pow, pow_succ]
          field_simp
  · rintro ⟨j, hj, hne⟩
    rw [hd]
    have hfj : 1 / (N : ℝ) ^ j ≤ f j := by
      simp only [hf]
      have hne' : ((x j : ℕ)) ≠ ((y j : ℕ)) := fun h => hne (Fin.ext h)
      have h1 : (1 : ℝ) ≤ |((x j : ℕ) : ℝ) - ((y j : ℕ) : ℝ)| := by
        rcases Nat.lt_or_gt_of_ne hne' with h | h
        · have : ((x j : ℕ) : ℝ) + 1 ≤ ((y j : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
        · have : ((y j : ℕ) : ℝ) + 1 ≤ ((x j : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]; linarith
      gcongr
    have hpow : 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ j := by
      gcongr
      · linarith
    calc 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ j := hpow
      _ ≤ f j := hfj
      _ ≤ ∑' k, f k := hs.le_tsum j (fun k _ => hfnn k)
