-- Prove2me | solution 1 for QAlgorithms.DeWolf.deutschJozsa_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:25:15.775807+00:00
-- url     : https://prove2.me/submissions/60a7453b-105d-46eb-be8a-e6d7a9746472

import Definitions.Def_QAlgorithms_Defs_Query

open QAlgorithms

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 * (2 : ℂ)^n = 1 := by
  have h : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 * 2 = 1 := by
    have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have : ((Real.sqrt (2 : ℝ))⁻¹)^2 * 2 = 1 := by field_simp; nlinarith
    exact_mod_cast this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, h, one_pow]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : act (A * B) ψ = act A (act B ψ) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private lemma act_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a i : ι) : act A (ket a) i = A i a := by
  simp [act, ket]


private lemma zero_amplitude (n : ℕ) (x : Qubits n → Bool) :
    deutschJozsaState x (fun _ => false) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))^2 *
        ∑ i : Qubits n, (if x i then (-1 : ℂ) else 1) := by
  classical
  rw [deutschJozsaState, act_mul, act_mul]
  change ∑ i : Qubits n, hadamardN n (fun _ => false) i *
    act (phaseOracle x) (act (hadamardN n) (zeroKet n)) i = _
  have hp (i : Qubits n) :
      act (phaseOracle x) (act (hadamardN n) (zeroKet n)) i =
        (if x i then (-1 : ℂ) else 1) *
          act (hadamardN n) (zeroKet n) i := by
    exact Matrix.mulVec_diagonal _ _ _
  simp_rw [hp, zeroKet, act_ket]
  have hz (i : Qubits n) : dotBits (fun _ : Fin n => false) i = false := by
    simp only [dotBits, Bool.false_and]
    change (∑ _ : Fin n, (0 : Bool)) = false
    simp only [Finset.sum_const_zero]
    rfl
  have hz' (i : Qubits n) : dotBits i (fun _ : Fin n => false) = false := by
    simpa only [dotBits, Bool.and_comm] using hz i
  simp only [hadamardN, Matrix.of_apply, hz, hz', Bool.false_eq_true, ↓reduceIte]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma oracle_sign_sum {ι : Type*} [Fintype ι] (x : ι → Bool) :
    (∑ i, if x i then (-1 : ℂ) else 1) =
      (Fintype.card ι : ℂ) - 2 * (hammingWeight x : ℂ) := by
  classical
  have h (i : ι) : (if x i then (-1 : ℂ) else 1) =
      1 - 2 * (if x i = true then (1 : ℂ) else 0) := by cases x i <;> norm_num
  simp_rw [h]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hammingWeight]

theorem solution (n : ℕ) (x : Qubits n → Bool) :
    (IsConstant x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 1) ∧
      (IsBalanced x → prob (deutschJozsaState x) (fun _ : Fin n => false) = 0) := by
  classical
  have hp : prob (deutschJozsaState x) (fun _ : Fin n => false) =
      ‖deutschJozsaState x (fun _ => false)‖ ^ 2 := by simp [prob, ket, EuclideanSpace.inner_single_left]
  rw [hp, zero_amplitude]
  constructor
  · intro hx
    have hc (i : Qubits n) : x i = x (fun _ => false) := hx i _
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_assoc, normalization]
    cases x (fun _ => false) <;> norm_num
  · intro hx
    rw [oracle_sign_sum]
    have hb : (2 : ℂ) * (hammingWeight x : ℂ) = (Fintype.card (Qubits n) : ℂ) := by
      exact_mod_cast hx
    rw [hb, sub_self, mul_zero, norm_zero, zero_pow (by decide)]
