-- Prove2me | solution 1 for RuntimeTransfer.fourier_oracle_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:28:01.011743+00:00
-- url     : https://prove2.me/submissions/f18d0f9f-071b-4067-ab74-7e9355a4691f

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_RuntimeTransferFourier
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RuntimeTransfer

theorem chirp_identity {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (x : Fin n → ℂ) :
    chirpDecode ρ (middleProduct (chirpQuery ρ x)) = fourierValue ρ x := by
  funext k
  simp only [chirpDecode, middleProduct, chirpQuery, fourierValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val ≤ k.val + n := by have := j.isLt; omega
  have hind : ((middleIndex k j).val : ℤ) - (n : ℤ) =
      (k.val : ℤ) - (j.val : ℤ) := by
    simp only [middleIndex, Nat.cast_sub hj, Nat.cast_add]
    ring
  rw [hind]
  calc
    ρ ^ ((k.val : ℤ) ^ 2) * (x j * ρ ^ ((j.val : ℤ) ^ 2) *
        ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) =
      x j * (ρ ^ ((k.val : ℤ) ^ 2) * ρ ^ ((j.val : ℤ) ^ 2) *
        ρ ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2)) := by ring
    _ = x j * ρ ^ ((k.val : ℤ)^2 + (j.val : ℤ)^2 -
        ((k.val : ℤ) - (j.val : ℤ))^2) := by
      rw [← zpow_add₀ hρ, ← zpow_add₀ hρ]
      rfl
    _ = x j * (ρ ^ 2) ^ (j.val * k.val) := by
      rw [show (k.val : ℤ)^2 + (j.val : ℤ)^2 -
        ((k.val : ℤ) - (j.val : ℤ))^2 = (2 * (j.val * k.val) : ℕ) by push_cast; ring]
      simp only [zpow_natCast, pow_mul]

end RuntimeTransfer

open RuntimeTransfer
theorem solution {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin n → ℂ) × ℕ)
    (T E D : ℕ) (hcorrect : ∀ q, (oracle q).1 = middleProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ T) :
    ((fourierProgram ρ x E D).run oracle).1 = fourierValue ρ x ∧
      ((fourierProgram ρ x E D).run oracle).2 ≤ E + D + T := by
  simp only [fourierProgram, Program.run, hcorrect]
  constructor
  · exact chirp_identity ρ hρ x
  · simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Nat.add_le_add_left (Nat.add_le_add_right (hcost (chirpQuery ρ x)) D) E

#print axioms solution
