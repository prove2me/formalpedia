-- Prove2me | solution 1 for RamanujanLostNotebook.PartIV.section_9_6_zeta_complex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T01:48:48.566547+00:00
-- url     : https://prove2.me/submissions/1b578fba-1551-4eef-83ec-5449f01c9e75

import Mathlib

theorem solution :
    Filter.Tendsto (fun s : ℂ => (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) - 1 / (s - 1))
      (nhdsWithin (1 : ℂ) {s : ℂ | 1 < s.re}) (nhds (Real.eulerMascheroniConstant : ℂ)) := by
  have hsub : nhdsWithin (1 : ℂ) {s : ℂ | 1 < s.re} ≤ nhdsWithin (1 : ℂ) {1}ᶜ := by
    apply nhdsWithin_mono
    intro s hs h1
    simp only [Set.mem_setOf_eq] at hs
    rw [Set.mem_singleton_iff] at h1
    rw [h1] at hs
    simp at hs
  refine ((tendsto_riemannZeta_sub_one_div).mono_left hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
