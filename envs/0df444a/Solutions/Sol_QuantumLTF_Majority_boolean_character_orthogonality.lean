-- Prove2me | solution 1 for QuantumLTF.Majority.boolean_character_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-16T20:28:51.212453+00:00
-- url     : https://prove2.me/submissions/715aa3f2-dffc-4435-acee-9d096661c0f2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Theorems.Thm_QuantumLTF_Majority_boolean_character_mul
import Theorems.Thm_QuantumLTF_Majority_boolean_character_total

open QAlgorithms
open QuantumLTF.Majority
open scoped symmDiff

theorem solution : ∀ k : ℕ, ∀ T U : Finset (Fin k),
    ∑ S : Qubits k,
      (-1 : ℤ) ^ ((T.filter fun i => S i).card) *
      (-1 : ℤ) ^ ((U.filter fun i => S i).card) =
        if T = U then (2 : ℤ)^k else 0 := by
  intro k T U
  simp_rw [boolean_character_mul k T U]
  rw [boolean_character_total k (T ∆ U)]
  simp
