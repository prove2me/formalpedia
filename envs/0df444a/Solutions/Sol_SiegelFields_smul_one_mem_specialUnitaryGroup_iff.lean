-- Prove2me | solution 1 for SiegelFields.smul_one_mem_specialUnitaryGroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:46:13.575931+00:00
-- url     : https://prove2.me/submissions/dff1b4fb-f778-4af7-a2f9-df82b62179fc

import Mathlib

open Matrix Complex

theorem solution (c : ℂ) :
    c • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ specialUnitaryGroup (Fin 2) ℂ ↔
      c = 1 ∨ c = -1 := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · rintro ⟨hU, hdet⟩
    have hc2 : c ^ 2 = 1 := by
      simpa [det_smul, det_one, Fintype.card_fin] using hdet
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp this with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (rfl | rfl)
    · constructor
      · simp [star_one]
      · simp [det_one]
    · constructor
      · simp [star_smul, star_neg, star_one, mul_smul, smul_mul, smul_smul]
      · rw [det_smul, det_one, Fintype.card_fin]
        norm_num
