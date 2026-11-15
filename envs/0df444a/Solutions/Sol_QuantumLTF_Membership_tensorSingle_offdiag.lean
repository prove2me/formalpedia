-- Prove2me | solution 1 for QuantumLTF.Membership.tensorSingle_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T22:09:14.20308+00:00
-- url     : https://prove2.me/submissions/00d90f38-ac4c-41ca-92f6-bb046bae40ca

import Mathlib
import Definitions.Def_QuantumLTF_Membership_tensorSingle

open QAlgorithms

theorem solution {b : ℕ} (u : Fin b → Matrix Bool Bool ℂ)
    (hu : ∀ i y z, y ≠ z → u i y z = 0)
    (y z : Qubits b) (hyz : y ≠ z) :
    QuantumLTF.Membership.tensorSingle u y z = 0 := by
  have hnot : ¬ ∀ i, y i = z i := by
    intro h
    exact hyz (funext h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  rw [QuantumLTF.Membership.tensorSingle, Matrix.of_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hu i (y i) (z i) hi)
