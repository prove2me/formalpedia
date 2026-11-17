-- Prove2me | solution 2 for QuantumLTF.Majority.boolean_character_mul
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-16T22:55:17.438954+00:00
-- url     : https://prove2.me/submissions/8252cfa9-1777-4b4c-b118-8d37426b4ffb

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Theorems.Thm_QuantumLTF_Majority_card_symmDiff_add_twice_inter

open QAlgorithms
open QuantumLTF.Majority
open scoped symmDiff

theorem solution : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∀ S : Qubits k,
    (-1 : ℤ) ^ ((T.filter fun i => S i).card) *
      (-1 : ℤ) ^ ((U.filter fun i => S i).card) =
        (-1 : ℤ) ^ (((T ∆ U).filter fun i => S i).card) := by
  intro k T U S
  let A := T.filter fun i => S i
  let B := U.filter fun i => S i
  have hfilter : (T ∆ U).filter (fun i => S i) = A ∆ B := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_symmDiff, A, B]
    aesop
  rw [hfilter]
  change (-1 : ℤ) ^ A.card * (-1 : ℤ) ^ B.card = (-1 : ℤ) ^ (A ∆ B).card
  rw [← pow_add]
  have hcard := card_symmDiff_add_twice_inter A B
  rw [← hcard, pow_add]
  have heven : (-1 : ℤ) ^ (2 * (A ∩ B).card) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, mul_one]

