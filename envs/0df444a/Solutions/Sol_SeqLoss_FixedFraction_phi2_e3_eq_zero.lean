-- Prove2me | solution 1 for SeqLoss.FixedFraction.phi2_e3_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:01:01.158931+00:00
-- url     : https://prove2.me/submissions/7e855245-f135-4efa-8ec4-1fe5c0736efb

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hmp : MergingProof φ) :
    φ 3 (elem 3) 1 = 0 := by
  obtain ⟨h1, h2⟩ := hmp
  have e3 := (hφ 3 (elem 3) (by intro i; unfold elem; split_ifs <;> norm_num)).1
  have e2 := (hφ 2 (elem 2) (by intro i; unfold elem; split_ifs <;> norm_num)).1
  obtain ⟨nn3, -, t3⟩ := e3
  obtain ⟨nn2, -, t2⟩ := e2
  have s3 : ∑ i, elem 3 i = 1 := by rw [Fin.sum_univ_three]; simp [elem]
  have s2 : ∑ i, elem 2 i = 1 := by rw [Fin.sum_univ_two]; simp [elem]
  rw [s3, Fin.sum_univ_three] at t3
  rw [s2, Fin.sum_univ_two] at t2
  have a0 := nn3 0
  have a1 := nn3 1
  have a2 := nn3 2
  exact le_antisymm (by linarith) a1
