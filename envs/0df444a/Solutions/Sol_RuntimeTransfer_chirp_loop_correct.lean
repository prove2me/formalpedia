-- Prove2me | solution 1 for RuntimeTransfer.chirp_loop_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:28:01.913314+00:00
-- url     : https://prove2.me/submissions/250f72b0-47e3-4f2b-81d9-f4aee514a00d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_RuntimeTransferArithmetic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RuntimeTransferFourier

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

theorem fourier_oracle_transfer {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
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

end RuntimeTransfer


set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RuntimeTransfer

theorem arithmetic_run_bind {n : ℕ} {R S : Type} (p : Arithmetic n R)
    (f : R → Arithmetic n S)
    (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ) :
    (p.bind f).run oracle =
      let a := p.run oracle
      let b := (f a.1).run oracle
      (b.1, a.2 + b.2) := by
  induction p with
  | done r => simp [Arithmetic.bind, Arithmetic.run]
  | mul a b next ih => simp [Arithmetic.bind, Arithmetic.run, ih, Nat.add_assoc]
  | inv a next ih => simp [Arithmetic.bind, Arithmetic.run, ih, Nat.add_assoc]
  | product q next ih => simp [Arithmetic.bind, Arithmetic.run, ih, Nat.add_assoc]

theorem full_product_middle {n : ℕ} (q : FourierQuery n) :
    productMiddle (fullProduct q) = middleProduct q := by
  funext k
  simp only [productMiddle, fullProduct, middleProduct]
  apply Finset.sum_congr rfl
  intro j _
  have h : j.val ≤ k.val + n ∧ k.val + n - j.val < 2 * n + 1 := by
    have := k.isLt; have := j.isLt; omega
  simp [h, middleIndex]

end RuntimeTransfer
open RuntimeTransfer
theorem solution {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (j : ℤ) (m : ℕ)
    (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ) :
    (chirpLoop (ρ ^ 2) (ρ ^ (j ^ 2)) (ρ ^ (2 * j + 1)) m).run oracle =
      ((fun i : Fin m => ρ ^ ((j + (i.val : ℤ)) ^ 2)), 2 * m) := by
  induction m generalizing j with
  | zero =>
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · rfl
  | succ m ih =>
    have hc : ρ ^ (j ^ 2) * ρ ^ (2 * j + 1) = ρ ^ ((j + 1) ^ 2) := by
      rw [← zpow_add₀ hρ]
      congr 1
      ring
    have hd : ρ ^ (2 * j + 1) * ρ ^ 2 = ρ ^ (2 * (j + 1) + 1) := by
      rw [← zpow_natCast ρ 2, ← zpow_add₀ hρ]
      congr 1
      ring
    simp only [chirpLoop, Arithmetic.run, hc, hd, arithmetic_run_bind, ih]
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun t => ?_) i
      · simp
      · simp only [Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
    · omega
#print axioms solution
