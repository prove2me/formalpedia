-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.strongest_interpolation_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:29:54.191802+00:00
-- url     : https://prove2.me/submissions/bfbf8532-111f-4e44-83fb-de7d50cabe34

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators

namespace X7Interp

/-- A discretely convex sequence has nondecreasing increments. -/
lemma incr_mono (u : ℕ → ℝ) (hu : ∀ k, 2 * u (k + 1) ≤ u k + u (k + 2)) :
    ∀ i j, i ≤ j → u (i + 1) - u i ≤ u (j + 1) - u j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => have := hu j; linarith

lemma sum_below (u : ℕ → ℝ) (hu : ∀ k, 2 * u (k + 1) ≤ u k + u (k + 2)) (m : ℕ) :
    u m - u 0 ≤ m * (u (m + 1) - u m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := incr_mono u hu m (m + 1) (by omega)
    have h2 : ((m : ℝ) + 1) * (u (m + 1) - u m) ≤ ((m : ℝ) + 1) * (u (m + 1 + 1) - u (m + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    push_cast
    nlinarith

lemma sum_above (u : ℕ → ℝ) (hu : ∀ k, 2 * u (k + 1) ≤ u k + u (k + 2)) (m : ℕ) :
    ∀ l : ℕ, (l : ℝ) * (u (m + 1) - u m) ≤ u (m + l) - u m := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    have := incr_mono u hu m (m + l) (by omega)
    push_cast
    rw [show m + (l + 1) = m + l + 1 by ring]
    linarith

end X7Interp

open QAlgorithms.Papers.Independent.Information100.P19 X7Interp in
theorem solution (N : ℕ) (s : Fin N → ℝ) (hs : s≠0) :
    ∀ a b : ℕ, 1≤a → a<b →
      interpolationRatio s a b ≤ interpolationRatio s 1 2 := by
  intro a b ha hab
  set M : ℕ → ℝ := fun k => ∑ i, |s i| ^ (2 * k) with hM
  obtain ⟨i0, hi0⟩ : ∃ i, s i ≠ 0 := by
    by_contra h; push_neg at h; exact hs (funext h)
  have hMpos : ∀ k, 0 < M k := by
    intro k
    have hle : |s i0| ^ (2 * k) ≤ M k :=
      Finset.single_le_sum (f := fun i => |s i| ^ (2 * k)) (fun i _ => by positivity)
        (Finset.mem_univ i0)
    have : 0 < |s i0| ^ (2 * k) := pow_pos (abs_pos.mpr hi0) _
    linarith
  -- log-convexity from Cauchy–Schwarz
  set u : ℕ → ℝ := fun k => Real.log (M (k + 1)) with hu
  have hconv : ∀ k, 2 * u (k + 1) ≤ u k + u (k + 2) := by
    intro k
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |s i| ^ (k + 1)) (fun i => |s i| ^ (k + 3))
    have e1 : ∑ i, |s i| ^ (k + 1) * |s i| ^ (k + 3) = M (k + 2) :=
      Finset.sum_congr rfl (fun i _ => by rw [← pow_add]; ring_nf)
    have e2 : ∑ i, (|s i| ^ (k + 1)) ^ 2 = M (k + 1) :=
      Finset.sum_congr rfl (fun i _ => by rw [← pow_mul]; ring_nf)
    have e3 : ∑ i, (|s i| ^ (k + 3)) ^ 2 = M (k + 3) :=
      Finset.sum_congr rfl (fun i _ => by rw [← pow_mul]; ring_nf)
    rw [e1, e2, e3] at cs
    simp only [hu]
    rw [show (2 : ℝ) * Real.log (M (k + 1 + 1)) = Real.log (M (k + 2) ^ 2) by
      rw [Real.log_pow]; norm_num, ← Real.log_mul (hMpos _).ne' (hMpos _).ne']
    exact Real.log_le_log (pow_pos (hMpos _) 2) cs
  -- the exponent inequality
  have hba : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have key : ((2 * b : ℕ) - 1 : ℝ) * u (a - 1) - ((2 * a : ℕ) - 1 : ℝ) * u (b - 1) ≤
      ((b : ℝ) - a) * (3 * u 0 - u 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = m + 1 + l := ⟨b - (m + 1), by omega⟩
    have hl : 1 ≤ l := by omega
    simp only [Nat.add_sub_cancel]
    rw [show m + 1 + l - 1 = m + l by omega]
    have F1 := sum_below u hconv m
    have F2 := sum_above u hconv m l
    have F3 := incr_mono u hconv 0 m (by omega)
    push_cast
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hm0 : (0 : ℝ) ≤ m := by positivity
    set D := u (m + 1) - u m
    nlinarith [mul_le_mul_of_nonneg_left F2 (by linarith : (0:ℝ) ≤ 2 * m + 1)]
  -- translate to the ratio
  unfold interpolationRatio
  have hMa : ∑ i, |s i| ^ (2 * a) = M a := rfl
  have hMb : ∑ i, |s i| ^ (2 * b) = M b := rfl
  have hM1 : ∑ i, |s i| ^ (2 * 1) = M 1 := rfl
  have hM2 : ∑ i, |s i| ^ (2 * 2) = M 2 := rfl
  simp only [Real.rpow_eq_pow]
  rw [hMa, hMb, hM1, hM2]
  rw [Real.rpow_def_of_pos (hMpos _), Real.rpow_def_of_pos (hMpos _),
    Real.rpow_def_of_pos (hMpos _), Real.rpow_def_of_pos (hMpos _), ← Real.exp_sub,
    ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have ua : u (a - 1) = Real.log (M a) := by simp only [hu]; congr 2; omega
  have ub : u (b - 1) = Real.log (M b) := by simp only [hu]; congr 2; omega
  have u0 : u 0 = Real.log (M 1) := rfl
  have u1 : u 1 = Real.log (M 2) := rfl
  rw [ua, ub, u0, u1] at key
  norm_num
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 < ((b : ℝ) - a)⁻¹ := inv_pos.mpr hba
  have := mul_le_mul_of_nonneg_right key hinv.le
  rw [mul_comm ((b : ℝ) - a), mul_assoc, mul_inv_cancel₀ hba.ne', mul_one] at this
  push_cast at this
  nlinarith [this]
