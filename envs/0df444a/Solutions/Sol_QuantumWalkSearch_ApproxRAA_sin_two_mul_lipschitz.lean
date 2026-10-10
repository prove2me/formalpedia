-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.sin_two_mul_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:05:16.828597+00:00
-- url     : https://prove2.me/submissions/19594dc3-c990-4bc7-a094-80d5787cacb7

import Mathlib

theorem solution (A B : ℝ) (hA : A ∈ Set.Icc 0 (Real.pi / 4))
    (hB : B ∈ Set.Icc 0 (Real.pi / 4)) :
    |Real.sin (2 * A) - Real.sin (2 * B)| ≤ 2 * |Real.sin A - Real.sin B| := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  have hpi := Real.pi_pos
  -- product-to-sum forms
  have h1 : Real.sin (2 * A) - Real.sin (2 * B) =
      2 * Real.sin ((2 * A - 2 * B) / 2) * Real.cos ((2 * A + 2 * B) / 2) := Real.sin_sub_sin _ _
  have h2 : Real.sin A - Real.sin B = 2 * Real.sin ((A - B) / 2) * Real.cos ((A + B) / 2) :=
    Real.sin_sub_sin _ _
  have e1 : (2 * A - 2 * B) / 2 = 2 * ((A - B) / 2) := by ring
  have e2 : (2 * A + 2 * B) / 2 = 2 * ((A + B) / 2) := by ring
  rw [h1, h2, e1, e2, Real.sin_two_mul, Real.cos_two_mul]
  -- c := cos((A+B)/2) ∈ [0,1]
  set c := Real.cos ((A + B) / 2) with hc
  have hc0 : 0 ≤ c := by
    apply Real.cos_nonneg_of_mem_Icc; constructor <;> linarith
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hcc : 0 ≤ 2 * c ^ 2 - 1 := by
    have : Real.cos (2 * ((A + B) / 2)) = 2 * c ^ 2 - 1 := Real.cos_two_mul _
    rw [← this]
    apply Real.cos_nonneg_of_mem_Icc; constructor <;> linarith
  have hcle : 2 * c ^ 2 - 1 ≤ c := by nlinarith
  have hd : |Real.cos ((A - B) / 2)| ≤ 1 := Real.abs_cos_le_one _
  set s := Real.sin ((A - B) / 2) with hs
  have hL : |2 * (2 * s * Real.cos ((A - B) / 2)) * (2 * c ^ 2 - 1)| =
      4 * |s| * |Real.cos ((A - B) / 2)| * (2 * c ^ 2 - 1) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hcc, abs_two]; ring
  have hR : |2 * s * c| = 2 * |s| * c := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_two]
  rw [hL, hR]
  have hs0 : 0 ≤ |s| := abs_nonneg _
  calc 4 * |s| * |Real.cos ((A - B) / 2)| * (2 * c ^ 2 - 1)
      ≤ 4 * |s| * 1 * (2 * c ^ 2 - 1) := by gcongr
    _ = 4 * |s| * (2 * c ^ 2 - 1) := by ring
    _ ≤ 4 * |s| * c := mul_le_mul_of_nonneg_left hcle (by positivity)
    _ = 2 * (2 * |s| * c) := by ring
