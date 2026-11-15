-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhase_exponent_sum
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T21:52:16.899193+00:00
-- url     : https://prove2.me/submissions/2063b3e3-43ca-4a82-94d8-07a4b32ff28c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Theorems.Thm_QAlgorithms_bitsToNat_cast_sum_complex

open QAlgorithms

theorem solution (b : ℕ) (z : Qubits b) :
    let N : ℂ := (2 : ℂ) ^ b
    let c : ℂ := -(1 / 2) + 1 / (2 * N)
    (∑ i : Fin b,
      ((if z i then c * (2 : ℂ) ^ (b - 1 - i.1) else 0) +
        N * c ^ 2 / (2 * b))) =
      c * (bitsToNat z : ℂ) + N * c ^ 2 / 2 := by
  dsimp
  cases b with
  | zero => simp [bitsToNat]
  | succ b =>
      rw [Finset.sum_add_distrib]
      have hw := bitsToNat_cast_sum_complex z
      rw [← hw]
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        split <;> simp_all
      · simp
        field_simp
