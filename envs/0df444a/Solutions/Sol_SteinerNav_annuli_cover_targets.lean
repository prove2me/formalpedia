-- Prove2me | solution 1 for SteinerNav.annuli_cover_targets
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:04:15.803799+00:00
-- url     : https://prove2.me/submissions/6740bd43-0420-417f-9ea6-6d99f2b986c0

import Mathlib
import Definitions.Def_SteinerNav_aspectRatio

open SteinerNav

theorem solution {d : ℕ} (hd : 1 ≤ d) (P : Finset (Pt d)) (hn : 2 ≤ P.card)
    (s t : Pt d) (hs : s ∈ P) (ht : t ∈ P) (hts : t ≠ s) :
    ∃ i < annulusCount P,
      (2 : ℝ) ^ i * minDist P ≤ dist s t ∧ dist s t ≤ (2 : ℝ) ^ (i + 1) * minDist P := by
  let offDiag : Finset (Pt d × Pt d) := (P ×ˢ P).filter fun e => e.1 ≠ e.2
  let Dset : Finset ℝ := offDiag.image fun e => dist e.1 e.2
  have hst_mem : (t, s) ∈ offDiag :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, hs⟩, hts⟩
  have hst_D : dist s t ∈ Dset := by
    rw [dist_comm s t]
    exact Finset.mem_image.mpr ⟨(t, s), hst_mem, rfl⟩
  have hne : Dset.Nonempty := ⟨dist s t, hst_D⟩
  have hset : {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y} = (Dset : Set ℝ) := by
    ext r
    simp only [Set.mem_setOf, Finset.mem_coe, Dset, offDiag, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, hx, y, hy, hne', rfl⟩
      exact ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
      exact ⟨x, hx, y, hy, hne', rfl⟩
  have hmin_eq : minDist P = Dset.min' hne := by
    rw [minDist, hset]
    exact IsLeast.csInf_eq (Finset.isLeast_min' Dset hne)
  have hmax_eq : maxDist P = Dset.max' hne := by
    rw [maxDist, hset]
    exact IsGreatest.csSup_eq (Finset.isGreatest_max' Dset hne)
  have hmin_mem : Dset.min' hne ∈ Dset := Finset.min'_mem Dset hne
  obtain ⟨⟨x₁, y₁⟩, hxy₁, hdist₁⟩ := Finset.mem_image.mp hmin_mem
  have hmin_pos : 0 < minDist P := by
    rw [hmin_eq, ← hdist₁]
    exact dist_pos.mpr (Finset.mem_filter.mp hxy₁).2
  have hst_ge : minDist P ≤ dist s t := by
    rw [hmin_eq]
    exact Finset.min'_le Dset _ hst_D
  have hst_le : dist s t ≤ maxDist P := by
    rw [hmax_eq]
    exact Finset.le_max' Dset _ hst_D
  let x : ℝ := dist s t / minDist P
  have hx1 : 1 ≤ x := (one_le_div hmin_pos).mpr hst_ge
  have hx_pos : 0 < x := by positivity
  have hxΔ : x ≤ aspectRatio P :=
    div_le_div_of_nonneg_right hst_le (le_of_lt hmin_pos)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb_nonneg : 0 ≤ Real.logb 2 x := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hx1) (le_of_lt hlog2)
  have hlogb_mono : Real.logb 2 x ≤ Real.logb 2 (aspectRatio P) := by
    rw [Real.logb, Real.logb]
    exact div_le_div_of_nonneg_right (Real.log_le_log hx_pos hxΔ) (le_of_lt hlog2)
  let i : ℕ := ⌊Real.logb 2 x⌋₊
  have hi_le : i ≤ ⌊Real.logb 2 (aspectRatio P)⌋₊ := Nat.floor_mono hlogb_mono
  have hi_lt : i < annulusCount P := by
    rw [annulusCount]
    omega
  refine ⟨i, hi_lt, ?_, ?_⟩
  · have hi_real : (i : ℝ) ≤ Real.logb 2 x := Nat.floor_le hlogb_nonneg
    have hpow_le : (2 : ℝ) ^ (i : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 x) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hi_real
    rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hx_pos] at hpow_le
    exact (le_div_iff₀ hmin_pos).mp hpow_le
  · have hi_lt1 : Real.logb 2 x < ((i + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one (Real.logb 2 x)
    have hpow_le : (2 : ℝ) ^ (Real.logb 2 x) ≤ (2 : ℝ) ^ ((i + 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hi_lt1)
    rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hx_pos] at hpow_le
    exact (div_le_iff₀ hmin_pos).mp hpow_le
