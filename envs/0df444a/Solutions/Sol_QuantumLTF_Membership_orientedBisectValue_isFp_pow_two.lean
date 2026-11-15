-- Prove2me | solution 1 for QuantumLTF.Membership.orientedBisectValue_isFp_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:46:16.815193+00:00
-- url     : https://prove2.me/submissions/817411bf-ddd7-4179-a468-cec829124624

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_IsFp
import Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_isFp

open QuantumLTF.Membership

theorem solution (s : ℤ) (m q : ℕ) (h : ℝ) :
    IsFp (m + q + 2) (q + 1)
      (orientedBisectValue s q (-((2 : ℝ) ^ m)) ((2 : ℝ) ^ m) h) := by
  have hp : IsFp (m + 1) 0 ((2 : ℝ) ^ m) := by
    refine ⟨Nat.zero_le _, (2 : ℤ) ^ m, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity), pow_succ]
      have hpos : 0 < (2 : ℤ) ^ m := by positivity
      nlinarith
    · norm_num
  have hn : IsFp (m + 1) 0 (-((2 : ℝ) ^ m)) := by
    refine ⟨Nat.zero_le _, -((2 : ℤ) ^ m), ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg (by positivity), pow_succ]
      have hpos : 0 < (2 : ℤ) ^ m := by positivity
      nlinarith
    · norm_num
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    orientedBisectValue_isFp s q (m + 1) 0
      (-((2 : ℝ) ^ m)) ((2 : ℝ) ^ m) h hn hp
