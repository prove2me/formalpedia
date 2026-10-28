-- Prove2me | solution 1 for RuntimeTransfer.fourier_asymptotic_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:28:04.160977+00:00
-- url     : https://prove2.me/submissions/43dc7c43-2c25-4cba-9570-1cb86aa21060

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

theorem chirp_loop_correct {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) (j : ℤ) (m : ℕ)
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

theorem multiply_vector_correct {n m : ℕ} (a b : Fin m → ℂ)
    (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ) :
    (multiplyVector m a b).run oracle = ((fun j => a j * b j), m) := by
  induction m with
  | zero =>
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · rfl
  | succ m ih =>
    simp only [multiplyVector, Arithmetic.run, arithmetic_run_bind, ih]
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun t => ?_) i <;> simp
    · omega

theorem reflect_chirp_correct {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0) :
    reflectChirp (fun j : Fin (n + 1) => (ρ⁻¹) ^ ((j.val : ℤ) ^ 2)) =
      (fun t : Fin (2 * n + 1) => ρ ^ (-((t.val : ℤ) - (n : ℤ)) ^ 2)) := by
  funext t
  simp only [reflectChirp, inv_zpow, ← zpow_neg]
  congr 1
  unfold reflectedIndex
  split_ifs with h
  · simp only [Nat.cast_sub h]
    ring
  · have ht : n ≤ t.val := by omega
    simp only [Nat.cast_sub ht]

theorem fourier_arithmetic_exact {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (hcorrect : ∀ q, (oracle q).1 = fullProduct q) :
    (fourierArithmetic ρ x).run oracle =
      (fourierValue ρ x, 6 * n + 7 + (oracle (chirpQuery ρ x)).2) := by
  have hp := chirp_loop_correct ρ hρ 0 (n + 1) oracle
  have hn := chirp_loop_correct ρ⁻¹ (inv_ne_zero hρ) 0 (n + 1) oracle
  simp only [zero_pow (by decide : 2 ≠ 0), zpow_zero, mul_zero, zero_add, zpow_one] at hp hn
  simp only [fourierArithmetic, Arithmetic.run, ← pow_two, arithmetic_run_bind,
    hp, hn, multiply_vector_correct, reflect_chirp_correct ρ hρ, restrictChirp]
  change ((fun j => ρ ^ ((j.val : ℤ) ^ 2) *
    productMiddle (oracle (chirpQuery ρ x)).1 j),
    1 + (1 + (1 + (2 * (n + 1) + (2 * (n + 1) +
      (n + ((oracle (chirpQuery ρ x)).2 + n))))))) = _
  rw [hcorrect, full_product_middle]
  apply Prod.ext
  · exact chirp_identity ρ hρ x
  · omega

theorem fourier_arithmetic_transfer {n : ℕ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (P : ℕ → ℕ) (hcorrect : ∀ q, (oracle q).1 = fullProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ P (2 * n + 1)) :
    ((fourierArithmetic ρ x).run oracle).1 = fourierValue ρ x ∧
      ((fourierArithmetic ρ x).run oracle).2 ≤ P (2 * n + 1) + 6 * n + 7 := by
  rw [fourier_arithmetic_exact ρ hρ x oracle hcorrect]
  constructor
  · rfl
  · have := hcost (chirpQuery ρ x)
    simp only
    omega

theorem fourier_same_order {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) (hρ : ρ ≠ 0)
    (x : Fin n → ℂ) (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (P : ℕ → ℕ) (C : ℕ) (hcorrect : ∀ q, (oracle q).1 = fullProduct q)
    (hcost : ∀ q, (oracle q).2 ≤ P (2 * n + 1))
    (hscale : P (2 * n + 1) ≤ C * P n) (hlinear : n ≤ P n) :
    ((fourierArithmetic ρ x).run oracle).1 = fourierValue ρ x ∧
      ((fourierArithmetic ρ x).run oracle).2 ≤ (C + 13) * P n := by
  have ht := fourier_arithmetic_transfer ρ hρ x oracle P hcorrect hcost
  refine ⟨ht.1, ht.2.trans ?_⟩
  calc
    P (2 * n + 1) + 6 * n + 7 ≤ C * P n + 13 * n := by omega
    _ ≤ C * P n + 13 * P n := Nat.add_le_add_left (Nat.mul_le_mul_left 13 hlinear) _
    _ = (C + 13) * P n := by ring

end RuntimeTransfer
open RuntimeTransfer
theorem solution (ρ : ℕ → ℂ) (x : (n : ℕ) → Fin n → ℂ)
    (oracles : (n : ℕ) → FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ)
    (P : ℕ → ℕ) (C : ℕ) (hρ : ∀ n, ρ n ≠ 0)
    (hcorrect : ∀ n q, (oracles n q).1 = fullProduct q)
    (hcost : ∀ n q, (oracles n q).2 ≤ P (2 * n + 1))
    (hscale : ∀ n, 1 ≤ n → P (2 * n + 1) ≤ C * P n)
    (hlinear : ∀ n, 1 ≤ n → n ≤ P n) :
    (∀ n, ((fourierArithmetic (ρ n) (x n)).run (oracles n)).1 = fourierValue (ρ n) (x n)) ∧
      BigOBound (fun n => ((fourierArithmetic (ρ n) (x n)).run (oracles n)).2) P := by
  constructor
  · intro n
    exact (fourier_arithmetic_transfer (ρ n) (hρ n) (x n) (oracles n) P
      (hcorrect n) (hcost n)).1
  · refine ⟨C + 13, by omega, 1, ?_⟩
    intro n hn
    exact (fourier_same_order hn (ρ n) (hρ n) (x n) (oracles n) P C
      (hcorrect n) (hcost n) (hscale n hn) (hlinear n hn)).2
#print axioms solution
