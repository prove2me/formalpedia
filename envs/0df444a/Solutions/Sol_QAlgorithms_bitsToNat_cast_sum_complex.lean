-- Prove2me | solution 1 for QAlgorithms.bitsToNat_cast_sum_complex
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T21:42:44.983928+00:00
-- url     : https://prove2.me/submissions/35e183ad-c4cc-48a0-b600-b38c00ab5799

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

theorem solution {n : ℕ} (z : Qubits n) :
    (∑ i : Fin n, if z i then (2 : ℂ) ^ (n - 1 - (i : ℕ)) else 0) =
      (bitsToNat z : ℂ) := by
  simp only [bitsToNat, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all
