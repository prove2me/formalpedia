-- Prove2me | solution 1 for RuntimeTransfer.chirp_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:28:00.442826+00:00
-- url     : https://prove2.me/submissions/f04648ee-2f4d-42b4-b920-a94ed64a216a

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_RuntimeTransferFourier
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RuntimeTransfer

end RuntimeTransfer

open RuntimeTransfer
theorem solution {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (x : Fin n → ℂ) :
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

#print axioms solution
