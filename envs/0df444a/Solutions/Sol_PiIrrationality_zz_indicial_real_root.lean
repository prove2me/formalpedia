-- Prove2me | solution 1 for PiIrrationality.zz_indicial_real_root
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:08:31.895484+00:00
-- url     : https://prove2.me/submissions/0dc78b6d-842c-4faf-8c2d-e0355c645f0c

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Set

/-- The indicial cubic of Zeilberger–Zudilin, equation (18). -/
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

theorem zzIndicial_real_root_exists :
    ∃ N : ℝ, 21851 < N ∧ N < 21852 ∧ zzIndicial N = 0 := by
  have hneg : zzIndicial 21851 < 0 := by
    unfold zzIndicial
    norm_num
  have hpos : 0 < zzIndicial 21852 := by
    unfold zzIndicial
    norm_num
  have hcont : ContinuousOn zzIndicial (Icc (21851 : ℝ) 21852) := by
    unfold zzIndicial
    fun_prop
  have hmem : (0 : ℝ) ∈ Ioo (zzIndicial 21851) (zzIndicial 21852) := ⟨hneg, hpos⟩
  obtain ⟨N, hN, hroot⟩ :=
    (intermediate_value_Ioo (by norm_num : (21851 : ℝ) ≤ 21852) hcont) hmem
  exact ⟨N, hN.1, hN.2, hroot⟩

theorem zzIndicial_real_root :
    ∃! N : ℝ, 21851 < N ∧ N < 21852 ∧ zzIndicial N = 0 := by
  obtain ⟨N, hN1, hN2, hroot⟩ := zzIndicial_real_root_exists
  refine ExistsUnique.intro N ⟨hN1, hN2, hroot⟩ ?_
  intro M ⟨hM1, hM2, hMroot⟩
  have hNmem : N ∈ Icc (21851 : ℝ) 21852 := ⟨hN1.le, hN2.le⟩
  have hMmem : M ∈ Icc (21851 : ℝ) 21852 := ⟨hM1.le, hM2.le⟩
  rcases lt_trichotomy N M with hNM | hEq | hMN
  · have := zzIndicial_strictMonoOn hNmem hMmem hNM
    linarith [hroot, hMroot]
  · exact hEq.symm
  · have := zzIndicial_strictMonoOn hMmem hNmem hMN
    linarith [hroot, hMroot]

theorem solution :
    ∃! N : ℝ, 21851 < N ∧ N < 21852 ∧
      108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0 := by
  simpa [zzIndicial] using zzIndicial_real_root
