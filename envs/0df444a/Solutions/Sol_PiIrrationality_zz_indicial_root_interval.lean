-- Prove2me | solution 1 for PiIrrationality.zz_indicial_root_interval
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:14:44.180538+00:00
-- url     : https://prove2.me/submissions/52ce3b58-c13a-426f-9135-7f2941b7024a

import Mathlib.Topology.Order.IntermediateValue
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
  have hx1 : (21851 : ℝ) ≤ x := hx.1
  have hy1 : (21851 : ℝ) ≤ y := hy.1
  have hy2 : y ≤ 21852 := hy.2
  have hx2 : x ≤ 21852 := hx.2
  have hsqx : (21851 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
  have hsqy : (21851 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
  have hxyb : (21851 : ℝ) ^ 2 ≤ y * x := by nlinarith
  have hquad : 3 * (21851 : ℝ) ^ 2 ≤ y ^ 2 + y * x + x ^ 2 := by linarith
  have hsum : y + x ≤ (21852 : ℝ) + 21852 := by linarith
  have hlow : 0 < 108 * (3 * (21851 : ℝ) ^ 2) - 2359989 * ((21852 : ℝ) + 21852) + 138304 := by
    norm_num
  have hpos : 0 < 108 * (y ^ 2 + y * x + x ^ 2) - 2359989 * (y + x) + 138304 := by
    have hge : 108 * (3 * (21851 : ℝ) ^ 2) - 2359989 * ((21852 : ℝ) + 21852) + 138304 ≤
        108 * (y ^ 2 + y * x + x ^ 2) - 2359989 * (y + x) + 138304 := by
      have hmul : 108 * (3 * (21851 : ℝ) ^ 2) ≤ 108 * (y ^ 2 + y * x + x ^ 2) := by
        exact mul_le_mul_of_nonneg_left hquad (by norm_num)
      have hlin : 2359989 * (y + x) ≤ 2359989 * ((21852 : ℝ) + 21852) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      linarith
    linarith
  have : 0 < zzIndicial y - zzIndicial x := by
    rw [hfac]
    exact mul_pos (sub_pos.mpr hxy) hpos
  linarith

theorem solution :
    ∃! N : ℝ,
      (2185169139621 : ℝ) / 10 ^ 8 < N ∧ N < (2185169139622 : ℝ) / 10 ^ 8 ∧
        108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0 := by
  let L : ℝ := (2185169139621 : ℝ) / 10 ^ 8
  let U : ℝ := (2185169139622 : ℝ) / 10 ^ 8
  have hneg : zzIndicial L < 0 := by
    unfold zzIndicial L
    norm_num
  have hpos : 0 < zzIndicial U := by
    unfold zzIndicial U
    norm_num
  have hcont : ContinuousOn zzIndicial (Icc L U) := by
    unfold zzIndicial
    fun_prop
  have hmem : (0 : ℝ) ∈ Ioo (zzIndicial L) (zzIndicial U) := ⟨hneg, hpos⟩
  obtain ⟨N, hN, hroot⟩ :=
    (intermediate_value_Ioo (by unfold L U; norm_num : L ≤ U) hcont) hmem
  refine ExistsUnique.intro N ⟨hN.1, hN.2, by simpa [zzIndicial] using hroot⟩ ?_
  intro M ⟨hM1, hM2, hMroot⟩
  have hNmem : N ∈ Icc (21851 : ℝ) 21852 := by
    constructor
    · have : (21851 : ℝ) ≤ L := by unfold L; norm_num
      linarith [hN.1]
    · have : U ≤ 21852 := by unfold U; norm_num
      linarith [hN.2]
  have hMmem : M ∈ Icc (21851 : ℝ) 21852 := by
    constructor
    · have : (21851 : ℝ) ≤ L := by unfold L; norm_num
      linarith [hM1]
    · have : U ≤ 21852 := by unfold U; norm_num
      linarith [hM2]
  have hMroot' : zzIndicial M = 0 := by simpa [zzIndicial] using hMroot
  have hNroot' : zzIndicial N = 0 := by simpa [zzIndicial] using hroot
  rcases lt_trichotomy N M with hNM | hEq | hMN
  · have := zzIndicial_strictMonoOn hNmem hMmem hNM
    linarith [hNroot', hMroot']
  · exact hEq.symm
  · have := zzIndicial_strictMonoOn hMmem hNmem hMN
    linarith [hNroot', hMroot']
