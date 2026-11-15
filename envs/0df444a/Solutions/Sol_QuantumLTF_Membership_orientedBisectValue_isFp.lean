-- Prove2me | solution 1 for QuantumLTF.Membership.orientedBisectValue_isFp
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:44:24.881701+00:00
-- url     : https://prove2.me/submissions/1d0ea881-35c3-4518-94ca-3403e120f3ba

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_IsFp
import Theorems.Thm_QuantumLTF_Membership_IsFp_midpoint

open QuantumLTF.Membership

theorem solution (s : ℤ) (q B f : ℕ) (lo hi h : ℝ)
    (hlo : IsFp B f lo) (hhi : IsFp B f hi) :
    IsFp (B + q + 1) (f + q + 1)
      (orientedBisectValue s q lo hi h) := by
  have refineFp : ∀ (B f : ℕ) (x : ℝ), IsFp B f x → IsFp (B + 1) (f + 1) x := by
    intro B f x hx
    rcases hx with ⟨hfb, k, hk, rfl⟩
    refine ⟨Nat.add_le_add_right hfb 1, 2 * k, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), pow_succ]
      nlinarith
    · push_cast
      rw [pow_succ]
      ring
  induction q generalizing B f lo hi with
  | zero =>
      simpa [orientedBisectValue] using IsFp.midpoint B f lo hi hlo hhi
  | succ q ih =>
      let mid := (lo + hi) / 2
      have hmid : IsFp (B + 1) (f + 1) mid := by
        simpa [mid] using IsFp.midpoint B f lo hi hlo hhi
      have hlo' : IsFp (B + 1) (f + 1) lo := refineFp B f lo hlo
      have hhi' : IsFp (B + 1) (f + 1) hi := refineFp B f hi hhi
      simp only [orientedBisectValue]
      split
      · split
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (B := B + 1) (f := f + 1) lo mid hlo' hmid
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (B := B + 1) (f := f + 1) mid hi hmid hhi'
      · split
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (B := B + 1) (f := f + 1) mid hi hmid hhi'
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (B := B + 1) (f := f + 1) lo mid hlo' hmid
