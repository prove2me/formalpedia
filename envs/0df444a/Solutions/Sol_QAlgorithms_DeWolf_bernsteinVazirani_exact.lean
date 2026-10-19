-- Prove2me | solution 1 for QAlgorithms.DeWolf.bernsteinVazirani_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:25:12.795297+00:00
-- url     : https://prove2.me/submissions/ff51508b-cc8f-4bf2-bd61-f4493f9dc4ab

import Definitions.Def_QAlgorithms_Defs_Query
import Mathlib.Algebra.BigOperators.Ring.Finset

open QAlgorithms

private def sgn (b : Bool) : ℂ := if b then -1 else 1

private lemma sgn_add (a b : Bool) : sgn (a + b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sgn_add, ih]

private lemma char_orth (n : ℕ) (a b : Qubits n) :
    (∑ i : Qubits n, sgn (dotBits a i) * sgn (dotBits b i)) =
      if a = b then (2 : ℂ)^n else 0 := by
  classical
  simp_rw [dotBits, sgn_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k v => sgn (a k && v) * sgn (b k && v))]
  have h (k : Fin n) :
      (∑ v : Bool, sgn (a k && v) * sgn (b k && v)) =
        if a k = b k then (2 : ℂ) else 0 := by
    cases a k <;> cases b k <;> norm_num [sgn, Bool.add_eq_xor, Bool.zero_eq_false]
  simp_rw [h]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma normalization (n : ℕ) :
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)) ^ 2 * (2 : ℂ)^n = 1 := by
  have h : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 2 * 2 = 1 := by
    have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have : ((Real.sqrt (2 : ℝ))⁻¹)^2 * 2 = 1 := by field_simp; nlinarith
    exact_mod_cast this
  push_cast at h ⊢
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, h, one_pow]

private lemma hadamard_involutive (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  classical
  have he (a b : Qubits n) : hadamardN n a b =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * sgn (dotBits a b) := by
    have hc : dotBits b a = dotBits a b := by simp [dotBits, Bool.and_comm]
    simp only [hadamardN, Matrix.of_apply, hc, sgn]
    split_ifs <;> ring
  ext a b
  simp_rw [Matrix.mul_apply, he]
  have hc (i : Qubits n) : dotBits i b = dotBits b i := by simp [dotBits, Bool.and_comm]
  simp_rw [hc]
  simp_rw [show ∀ u v : ℂ, (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * u *
    ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * v) =
      ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ))^2 * (u * v) by intros; ring]
  rw [← Finset.mul_sum, char_orth]
  by_cases h : a = b
  · subst b
    simpa only [ite_true, Matrix.one_apply_eq] using normalization n
  · simp [h]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : act (A * B) ψ = act A (act B ψ) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

private lemma act_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a i : ι) : act A (ket a) i = A i a := by
  simp [act, ket]

private lemma phase_prepares (n : ℕ) (a : Qubits n) :
    act (phaseOracle (bvInput a)) (act (hadamardN n) (zeroKet n)) =
      act (hadamardN n) (ket a) := by
  ext i
  change (Matrix.diagonal (fun i => if bvInput a i then (-1 : ℂ) else 1)).mulVec
    (fun i => act (hadamardN n) (zeroKet n) i) i = act (hadamardN n) (ket a) i
  rw [Matrix.mulVec_diagonal]
  rw [zeroKet, act_ket, act_ket]
  have hc : dotBits a i = dotBits i a := by simp [dotBits, Bool.and_comm]
  have hz : dotBits (fun _ : Fin n => false) i = false := by
    simp only [dotBits, Bool.false_and]
    change (∑ _ : Fin n, (0 : Bool)) = false
    simp only [Finset.sum_const_zero]
    rfl
  simp only [hadamardN, Matrix.of_apply, bvInput, hc, hz, Bool.false_eq_true, ↓reduceIte]
  by_cases hd : dotBits i a = true <;> simp [hd]

theorem solution (n : ℕ) (a : Qubits n) :
    deutschJozsaState (bvInput a) = ket a ∧ prob (deutschJozsaState (bvInput a)) a = 1 := by
  have h : deutschJozsaState (bvInput a) = ket a := by
    rw [deutschJozsaState, act_mul, act_mul, phase_prepares, ← act_mul,
      hadamard_involutive]
    simp [act]
  refine ⟨h, ?_⟩
  rw [h]
  simp [prob, ket]
