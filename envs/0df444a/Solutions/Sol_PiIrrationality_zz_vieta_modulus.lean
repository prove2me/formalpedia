-- Prove2me | solution 1 for PiIrrationality.zz_vieta_modulus
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:31:15.88898+00:00
-- url     : https://prove2.me/submissions/823b74b1-5918-4d25-9439-890bf504023b

import Mathlib.Tactic

open Set

def zzIndicial (N : ℝ) : ℝ :=
  108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048

theorem zzIndicial_strictMonoOn :
    StrictMonoOn zzIndicial (Icc (21851 : ℝ) 21852) := by
  intro x hx y hy hxy
  have hfac : zzIndicial y - zzIndicial x =
      (y - x) * (108 * (y ^ 2 + y * x + x ^ 2) - 2359989 * (y + x) + 138304) := by
    unfold zzIndicial
    ring
  have hsqx : (21851 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith [hx.1, hx.2]
  have hsqy : (21851 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith [hy.1, hy.2]
  have hxyb : (21851 : ℝ) ^ 2 ≤ y * x := by nlinarith [hx.1, hy.1, hxy]
  have hquad : 3 * (21851 : ℝ) ^ 2 ≤ y ^ 2 + y * x + x ^ 2 := by linarith
  have hsum : y + x ≤ (21852 : ℝ) + 21852 := by linarith [hx.2, hy.2]
  have hlow : 0 < 108 * (3 * (21851 : ℝ) ^ 2) - 2359989 * ((21852 : ℝ) + 21852) + 138304 := by
    norm_num
  have hpos : 0 < 108 * (y ^ 2 + y * x + x ^ 2) - 2359989 * (y + x) + 138304 := by
    have hmul : 108 * (3 * (21851 : ℝ) ^ 2) ≤ 108 * (y ^ 2 + y * x + x ^ 2) :=
      mul_le_mul_of_nonneg_left hquad (by norm_num)
    have hlin : 2359989 * (y + x) ≤ 2359989 * ((21852 : ℝ) + 21852) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    linarith [hlow, hmul, hlin]
  have : 0 < zzIndicial y - zzIndicial x := by
    rw [hfac]
    exact mul_pos (sub_pos.mpr hxy) hpos
  linarith

def discNum (N : ℝ) : ℝ :=
  -254878812 * N ^ 2 + 5569533143289 * N - 663552

theorem discNum_strictAntiOn :
    StrictAntiOn discNum (Icc (21851 : ℝ) 21852) := by
  intro x hx y hy hxy
  have hfac : discNum y - discNum x =
      (y - x) * (-254878812 * (x + y) + 5569533143289) := by
    unfold discNum
    ring
  have hsum : (21851 : ℝ) + 21851 ≤ x + y := by linarith [hx.1, hy.1]
  have hcoef : -254878812 * (x + y) ≤ -254878812 * ((21851 : ℝ) + 21851) :=
    mul_le_mul_of_nonpos_left hsum (by norm_num)
  have hslope : -254878812 * (x + y) + 5569533143289 < 0 := by
    have hleft : -254878812 * ((21851 : ℝ) + 21851) + 5569533143289 < 0 := by norm_num
    linarith
  have : discNum y - discNum x < 0 := by
    rw [hfac]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hslope
  linarith

theorem solution (N : ℝ) (hlo : (21851 : ℝ) < N) (hhi : N < 21852)
    (hroot : 108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0) :
    (108 * N - 2359989) ^ 2 - 432 * (2048 / N) < 0 ∧
      (2048 / N) / 108 = 512 / (27 * N) := by
  let M : ℝ := (21851691396219 : ℝ) / 10 ^ 9
  have hMlo : (21851 : ℝ) < M := by unfold M; norm_num
  have hMhi : M < 21852 := by unfold M; norm_num
  have hfM : zzIndicial M < 0 := by unfold zzIndicial M; norm_num
  have hdiscM : discNum M < 0 := by unfold discNum M; norm_num
  have hNmem : N ∈ Icc (21851 : ℝ) 21852 := ⟨hlo.le, hhi.le⟩
  have hMmem : M ∈ Icc (21851 : ℝ) 21852 := ⟨hMlo.le, hMhi.le⟩
  have hMN : M < N := by
    rcases lt_trichotomy M N with hlt | heq | hgt
    · exact hlt
    · have : zzIndicial M = 0 := by simpa [heq, zzIndicial] using hroot
      linarith
    · have := zzIndicial_strictMonoOn hNmem hMmem hgt
      have hroot' : zzIndicial N = 0 := by simpa [zzIndicial] using hroot
      linarith
  have hdisc : discNum N < 0 := by
    have := discNum_strictAntiOn hMmem hNmem hMN
    linarith
  have hN0 : N ≠ 0 := by linarith
  have hid : N * ((108 * N - 2359989) ^ 2 - 432 * (2048 / N)) = discNum N := by
    have hring :
        N * (108 * N - 2359989) ^ 2 - 884736 - discNum N =
          108 * zzIndicial N := by
      unfold discNum zzIndicial
      ring
    have hroot' : zzIndicial N = 0 := by simpa [zzIndicial] using hroot
    have hclear : N * (432 * (2048 / N)) = (884736 : ℝ) := by
      field_simp
      norm_num
    have hsplit : N * ((108 * N - 2359989) ^ 2 - 432 * (2048 / N)) =
        N * (108 * N - 2359989) ^ 2 - N * (432 * (2048 / N)) := by ring
    rw [hsplit, hclear]
    have : N * (108 * N - 2359989) ^ 2 - 884736 - discNum N = 0 := by
      rw [hring, hroot']
      ring
    linarith
  refine ⟨?_, ?_⟩
  · have hneg : N * ((108 * N - 2359989) ^ 2 - 432 * (2048 / N)) < 0 := by
      rw [hid]
      exact hdisc
    rw [← mul_zero N] at hneg
    exact lt_of_mul_lt_mul_left hneg (by linarith)
  · field_simp
    ring
