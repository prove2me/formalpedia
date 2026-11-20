-- Prove2me | solution 1 for WangRenyiEntropy.Noninteger.power_sum_ratio
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:20:26.408116+00:00
-- url     : https://prove2.me/submissions/8bf04e56-36d6-4cc4-8753-c5e32d711b88

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

open Finset

/-- superadditivity of `x ^ q`, `q ≥ 1`, on nonnegative reals -/
lemma sum_rpow_le_rpow_sum' {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) {q : ℝ} (hq : 1 ≤ q) :
    ∑ i, a i ^ q ≤ (∑ i, a i) ^ q := by
  set S := ∑ i, a i with hS
  have hS0 : 0 ≤ S := sum_nonneg (fun i _ => ha i)
  have hle : ∀ i, a i ≤ S := fun i => single_le_sum (fun j _ => ha j) (mem_univ i)
  calc ∑ i, a i ^ q = ∑ i, a i * a i ^ (q - 1) := by
        refine sum_congr rfl (fun i _ => ?_)
        rcases (ha i).eq_or_lt with h | h
        · rw [← h, Real.zero_rpow (by linarith), zero_mul]
        · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring
    _ ≤ ∑ i, a i * S ^ (q - 1) := by
        refine sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i))
        exact Real.rpow_le_rpow (ha i) (hle i) (by linarith)
    _ = S ^ q := by
        rw [← sum_mul, ← hS]
        rcases hS0.eq_or_lt with h | h
        · rw [← h, zero_mul, Real.zero_rpow (by linarith)]
        · rw [← Real.rpow_one_add' h.le (by linarith)]; congr 1; ring

/-- Jensen / power mean: `(∑ b) ^ s ≤ d ^ (s - 1) ∑ b ^ s` for `s ≥ 1` -/
lemma jensen' {d : ℕ} (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) {s : ℝ} (hs : 1 ≤ s) :
    (∑ i, b i) ^ s ≤ (d : ℝ) ^ (s - 1) * ∑ i, b i ^ s := by
  have := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := (univ : Finset (Fin d))) hs
    (fun i _ => hb i)
  simpa using this

theorem solution (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≠ 1)
    (d : ℕ) (hd : 1 ≤ d) (p : WangRenyiEntropy.Noninteger.Law d) :
    WangRenyiEntropy.Noninteger.powerSum (2 * α - 1) p /
      (WangRenyiEntropy.Noninteger.powerSum α p) ^ 2 ≤ Real.rpow d |1 - 1 / α| := by
  obtain ⟨hp0, hp1⟩ := p.2
  set f : Fin d → ℝ := p.val with hf
  have hα0 : 0 < α := by linarith
  have hr0 : 0 < 2 * α - 1 := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold WangRenyiEntropy.Noninteger.powerSum
  change (∑ i, f i ^ (2 * α - 1)) / (∑ i, f i ^ α) ^ 2 ≤ (d : ℝ) ^ |1 - 1 / α|
  set A := ∑ i, f i ^ α with hA
  set B := ∑ i, f i ^ (2 * α - 1) with hB
  have hfα : ∀ i, 0 ≤ f i ^ α := fun i => Real.rpow_nonneg (hp0 i) _
  have hB0 : 0 ≤ B := sum_nonneg (fun i _ => Real.rpow_nonneg (hp0 i) _)
  -- `f ^ (2α-1) = (f ^ α) ^ q`
  set q := (2 * α - 1) / α with hq
  have hpow : ∀ i, f i ^ (2 * α - 1) = (f i ^ α) ^ q := by
    intro i; rw [← Real.rpow_mul (hp0 i)]; congr 1; rw [hq]; field_simp
  -- A > 0
  have hA0 : 0 < A := by
    by_contra h
    push Not at h
    have hz : ∀ i, f i ^ α = 0 := fun i =>
      le_antisymm ((single_le_sum (fun j _ => hfα j) (mem_univ i)).trans h) (hfα i)
    have : ∀ i, f i = 0 := fun i => by
      have := hz i
      rcases (hp0 i).eq_or_lt with h' | h'
      · exact h'.symm
      · exact absurd this (Real.rpow_pos_of_pos h' _).ne'
    simp [this] at hp1
  rcases lt_or_gt_of_ne hα1 with hlt | hgt
  · -- 1/2 < α < 1
    have habs : |1 - 1 / α| = 1 - q := by
      rw [abs_of_nonpos]
      · rw [hq]; field_simp; ring
      · rw [sub_nonpos, le_div_iff₀ hα0]; linarith
    rw [habs]
    have hq0 : 0 < q := div_pos hr0 hα0
    have hq1 : q < 1 := by rw [hq, div_lt_one hα0]; linarith
    -- power mean: B ≤ d^(1-q) A^q
    have hJ := jensen' (fun i => f i ^ (2 * α - 1)) (fun i => Real.rpow_nonneg (hp0 i) _)
      (s := 1 / q) (by rw [le_div_iff₀ hq0]; linarith)
    have hJ' : (∑ i, (f i ^ (2 * α - 1)) ^ (1 / q)) = A := by
      refine sum_congr rfl (fun i _ => ?_)
      rw [hpow i, ← Real.rpow_mul (hfα i), mul_one_div_cancel hq0.ne', Real.rpow_one]
    rw [hJ'] at hJ
    have hBq : B ≤ (d : ℝ) ^ (1 - q) * A ^ q := by
      have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hB0 _) hJ hq0.le
      rw [← Real.rpow_mul hB0, one_div_mul_cancel hq0.ne', Real.rpow_one,
        Real.mul_rpow (Real.rpow_nonneg hd0.le _) hA0.le, ← Real.rpow_mul hd0.le] at h2
      convert h2 using 3; field_simp
    -- A ≥ 1
    have hA1 : 1 ≤ A := by
      rw [← hp1]
      refine sum_le_sum (fun i _ => ?_)
      have hfi1 : f i ≤ 1 := hp1 ▸ single_le_sum (fun j _ => hp0 j) (mem_univ i)
      simpa using Real.rpow_le_rpow_of_exponent_ge' (hp0 i) hfi1 hα0.le hlt.le
    have hAq : A ^ q / A ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc A ^ q ≤ A ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
        _ = A ^ 2 := by norm_cast
    calc B / A ^ 2 ≤ (d : ℝ) ^ (1 - q) * A ^ q / A ^ 2 := by gcongr
      _ = (d : ℝ) ^ (1 - q) * (A ^ q / A ^ 2) := by ring
      _ ≤ (d : ℝ) ^ (1 - q) * 1 := by gcongr
      _ = (d : ℝ) ^ (1 - q) := mul_one _
  · -- α > 1
    have habs : |1 - 1 / α| = 1 - 1 / α := by
      rw [abs_of_nonneg]; rw [sub_nonneg, div_le_one hα0]; linarith
    rw [habs]
    have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hα0]; linarith
    have hBA : B ≤ A ^ q := by
      have := sum_rpow_le_rpow_sum' (fun i => f i ^ α) hfα hq1
      simpa [← hpow] using this
    -- Jensen: 1 ≤ d^(α-1) A
    have hJ := jensen' f hp0 (s := α) hgt.le
    rw [hp1, Real.one_rpow] at hJ
    -- A^(q-2) = A^(-1/α) ≤ d^(1-1/α)
    have hkey : A ^ q / A ^ 2 ≤ (d : ℝ) ^ (1 - 1 / α) := by
      have e : A ^ q / A ^ 2 = (A ^ (-1 / α)) := by
        rw [show (A ^ 2 : ℝ) = A ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hA0]
        congr 1; rw [hq]; field_simp; ring
      rw [e]
      -- A ≥ d^(1-α)
      have hAd : (d : ℝ) ^ (1 - α) ≤ A := by
        have h1 : (d : ℝ) ^ (1 - α) * ((d : ℝ) ^ (α - 1) * A) = A := by
          rw [← mul_assoc, ← Real.rpow_add hd0]; simp
        calc (d : ℝ) ^ (1 - α) = (d : ℝ) ^ (1 - α) * 1 := (mul_one _).symm
          _ ≤ (d : ℝ) ^ (1 - α) * ((d : ℝ) ^ (α - 1) * A) := by gcongr
          _ = A := h1
      have h2 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd0 _) hAd
        (show -1 / α ≤ 0 by rw [div_nonpos_iff]; right; exact ⟨by norm_num, hα0.le⟩)
      rw [← Real.rpow_mul hd0.le] at h2
      convert h2 using 2; field_simp; ring
    calc B / A ^ 2 ≤ A ^ q / A ^ 2 := by gcongr
      _ ≤ _ := hkey

