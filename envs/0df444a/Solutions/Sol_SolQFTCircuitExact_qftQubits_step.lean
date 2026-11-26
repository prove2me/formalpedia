-- Prove2me | solution 1 for SolQFTCircuitExact.qftQubits_step
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:54.168479+00:00
-- url     : https://prove2.me/submissions/a8e652bf-7594-473e-b06d-5fc34b5acd53

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib
section
set_option autoImplicit false

open QAlgorithms
open scoped Matrix BigOperators

namespace SolQFTCircuitExact





































































/-- Decomposition of `bitsToNat` via `j 0` and `Fin.tail j`. -/
lemma bitsToNat_cons {n : ℕ} (j : Qubits (n + 1)) :
    bitsToNat j = (if j 0 then 2 ^ n else 0) + bitsToNat (Fin.tail j) := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero,
    Fin.tail]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : n - (i.succ : ℕ) = n - 1 - (i : ℕ) := by
    rw [Fin.val_succ]
    omega
  rw [hsub]
  rfl

/-- Decomposition of `bitsToNat` via `Fin.init k` and `k (Fin.last n)`. -/
lemma bitsToNat_snoc {n : ℕ} (k : Qubits (n + 1)) :
    bitsToNat k = 2 * bitsToNat (Fin.init k) + (if k (Fin.last n) then 1 else 0) := by
  simp only [bitsToNat, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    Nat.add_sub_cancel, Nat.sub_self, pow_zero, Fin.init, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hsub : n - (i : ℕ) = (n - 1 - (i : ℕ)) + 1 := by omega
  rw [hsub, pow_succ']
  by_cases h : k i.castSucc = true <;> simp [h]

lemma phaseDiag_eq_exp {n : ℕ} (u : Qubits n) (b : Bool) :
    (∏ m : Fin n,
      if u m && b then
        Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
      else 1) =
    Complex.exp (2 * Real.pi * Complex.I *
      ((bitsToNat u : ℂ) * (if b then 1 else 0)) / (2 ^ (n + 1) : ℂ)) := by
  have hterm : ∀ m : Fin n,
      (if u m && b then
        Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
      else 1) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((if u m then 2 ^ (n - 1 - (m : ℕ)) else 0 : ℕ) : ℂ) * (if b then 1 else 0)) /
          (2 ^ (n + 1) : ℂ)) := by
    intro m
    have hm := m.isLt
    have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ (n - 1 - (m : ℕ)) * (2 : ℂ) ^ ((m : ℕ) + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : (2 : ℂ) ^ (n - 1 - (m : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    cases u m <;> cases b <;> simp
    congr 1
    rw [hpow, mul_comm ((2 : ℂ) ^ (n - 1 - (m : ℕ))) ((2 : ℂ) ^ ((m : ℕ) + 2)),
      mul_div_mul_right _ _ hne]
  simp_rw [hterm, ← Complex.exp_sum]
  congr 1
  simp only [bitsToNat, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_div]

lemma hadamard_eq_exp (n : ℕ) (a b : Bool) :
    hadamard a b =
      Complex.exp (2 * Real.pi * Complex.I *
        (((if a then 2 ^ n else 0 : ℕ) : ℂ) * (if b then 1 else 0)) / (2 ^ (n + 1) : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  have hpow : (2 : ℂ) ^ (n + 1) = 2 * (2 : ℂ) ^ n := by
    rw [pow_succ']
  have hne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpi : Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ n / (2 ^ (n + 1) : ℂ)) = -1 := by
    rw [hpow, mul_div_mul_right _ _ hne]
    rw [show (2 * Real.pi * Complex.I / 2 : ℂ) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  cases a <;> cases b <;>
    simp only [hadamard, Matrix.of_apply, Bool.and_self, Bool.and_false, Bool.false_and,
      ↓reduceIte, Bool.false_eq_true, Nat.cast_zero, mul_zero, zero_div,
      Complex.exp_zero, one_div, Nat.cast_pow, Nat.cast_ofNat, mul_one]
  · rw [hpi]
    ring

lemma exp_two_pi_I_nat (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  rw [show 2 * Real.pi * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I m

lemma qftQubits_apply (n : ℕ) (j k : Qubits n) :
    qftQubits n j k =
      Complex.exp (2 * Real.pi * Complex.I * ((bitsToNat j : ℂ) * (bitsToNat k : ℂ)) /
        (2 ^ n : ℂ)) / (Real.sqrt (2 ^ n) : ℂ) := by
  simp [qftQubits, qftMatrix, bitsEquivFin_apply]











end SolQFTCircuitExact




end
set_option autoImplicit false
open QAlgorithms
open scoped Matrix BigOperators
namespace SolQFTCircuitExact
end SolQFTCircuitExact
open SolQFTCircuitExact
theorem solution (n : ℕ) (j k : Qubits (n + 1)) :
    hadamard (j 0) (k (Fin.last n)) *
      ((∏ m : Fin n,
          if Fin.tail j m && k (Fin.last n) then
            Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
          else 1) *
        qftQubits n (Fin.tail j) (Fin.init k)) =
      qftQubits (n + 1) j k := by
  rw [SolQFTCircuitExact.hadamard_eq_exp n (j 0) (k (Fin.last n)), SolQFTCircuitExact.phaseDiag_eq_exp (Fin.tail j) (k (Fin.last n)),
    SolQFTCircuitExact.qftQubits_apply n (Fin.tail j) (Fin.init k), SolQFTCircuitExact.qftQubits_apply (n + 1) j k]
  have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt (2 ^ n) : ℂ) = (Real.sqrt (2 ^ (n + 1)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
    congr 2
    ring
  have hdiv : ∀ a b c s1 s2 : ℂ, (a / s1) * (b * (c / s2)) = (a * b * c) / (s1 * s2) := by
    intro a b c s1 s2
    ring
  rw [hdiv, hsqrt, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h1 : Complex.exp (2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (bitsToNat (Fin.init k) : ℂ) * 2) /
        (2 ^ (n + 1) : ℂ)) = 1 := by
    have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by rw [pow_succ]
    cases j 0
    · simp
    · simp only [↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
      have hne : (2 : ℂ) ^ n * 2 ≠ 0 := pow_ne_zero (n + 1) (by norm_num)
      rw [hpow,
        show 2 * Real.pi * Complex.I * ((2 : ℂ) ^ n * (bitsToNat (Fin.init k) : ℂ) * 2) =
          (2 * Real.pi * Complex.I * (bitsToNat (Fin.init k) : ℂ)) * ((2 : ℂ) ^ n * 2) by ring,
        mul_div_cancel_right₀ _ hne]
      exact SolQFTCircuitExact.exp_two_pi_I_nat (bitsToNat (Fin.init k))
  let A : ℂ :=
    2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (if k (Fin.last n) then 1 else 0)) / (2 ^ (n + 1) : ℂ) +
    2 * Real.pi * Complex.I *
      ((bitsToNat (Fin.tail j) : ℂ) * (if k (Fin.last n) then 1 else 0)) / (2 ^ (n + 1) : ℂ) +
    2 * Real.pi * Complex.I *
      ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ)) / (2 ^ n : ℂ)
  let C : ℂ :=
    2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (bitsToNat (Fin.init k) : ℂ) * 2) /
      (2 ^ (n + 1) : ℂ)
  calc Complex.exp A
    _ = Complex.exp A * 1 := (mul_one _).symm
    _ = Complex.exp A * Complex.exp C := by rw [h1]
    _ = Complex.exp (A + C) := (Complex.exp_add A C).symm
    _ = Complex.exp (2 * Real.pi * Complex.I * ((bitsToNat j : ℂ) * (bitsToNat k : ℂ)) /
          (2 ^ (n + 1) : ℂ)) := by
      congr 1
      dsimp only [A, C]
      have hj : (bitsToNat j : ℂ) =
          ((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) + (bitsToNat (Fin.tail j) : ℂ) := by
        exact_mod_cast SolQFTCircuitExact.bitsToNat_cons j
      have hk : (bitsToNat k : ℂ) =
          2 * (bitsToNat (Fin.init k) : ℂ) + ((if k (Fin.last n) then 1 else 0 : ℕ) : ℂ) := by
        exact_mod_cast SolQFTCircuitExact.bitsToNat_snoc k
      have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by rw [pow_succ]
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      have hscale :
          2 * Real.pi * Complex.I * ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ)) /
            (2 ^ n : ℂ) =
          2 * Real.pi * Complex.I *
            ((bitsToNat (Fin.tail j) : ℂ) * (2 * (bitsToNat (Fin.init k) : ℂ))) /
            (2 ^ (n + 1) : ℂ) := by
        rw [hpow,
          show 2 * Real.pi * Complex.I *
              ((bitsToNat (Fin.tail j) : ℂ) * (2 * (bitsToNat (Fin.init k) : ℂ))) =
            (2 * Real.pi * Complex.I * ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ))) * 2 by ring,
          mul_div_mul_right _ _ h2ne]
      rw [hj, hk, hscale]
      cases k (Fin.last n) <;>
        simp only [↓reduceIte, Bool.false_eq_true, Nat.cast_one, Nat.cast_zero] <;>
        ring
