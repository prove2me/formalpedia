-- Prove2me | solution 1 for TranscendenceTheory.small_polynomials_of_small_integral_elements
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T03:16:37.243314+00:00
-- url     : https://prove2.me/submissions/866fc255-3fd2-40d7-aa7f-4bc4e6bcb24f

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Convert

open Polynomial Matrix
open scoped Polynomial

namespace TranscendenceTheory.IntegralNorm

noncomputable def length (p : ℤ[X]) : ℝ := p.sum fun _ a ↦ ‖a‖

lemma length_nonneg (p : ℤ[X]) : 0 ≤ length p :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

lemma length_eq_sum_range (p : ℤ[X]) (D : ℕ) (hD : p.natDegree < D) :
    length p = ∑ k ∈ Finset.range D, ‖p.coeff k‖ := by
  exact Polynomial.sum_eq_of_subset _ (fun _ ↦ norm_zero) (by
    intro k hk
    exact Finset.mem_range.mpr ((le_natDegree_of_mem_supp k hk).trans_lt hD))

lemma length_zero : length 0 = 0 := by simp [length]

lemma length_monomial (k : ℕ) (a : ℤ) : length (monomial k a) = ‖a‖ := by
  simp [length]

lemma length_add_le (p q : ℤ[X]) : length (p + q) ≤ length p + length q := by
  let D := max p.natDegree q.natDegree + 1
  rw [length_eq_sum_range (p + q) D (lt_of_le_of_lt (natDegree_add_le p q) (by omega)),
    length_eq_sum_range p D (by omega), length_eq_sum_range q D (by omega),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ ↦ by simpa using norm_add_le (p.coeff k) (q.coeff k)

lemma length_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    length (∑ i ∈ s, f i) ≤ ∑ i ∈ s, length (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [length_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (length_add_le _ _).trans (add_le_add_right ih _)

lemma length_mul_le (p q : ℤ[X]) : length (p * q) ≤ length p * length q := by
  rw [Polynomial.mul_eq_sum_sum]
  calc
    _ ≤ ∑ i ∈ p.support, length (q.sum fun j b ↦ monomial (i + j) (p.coeff i * b)) :=
      length_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, ‖p.coeff i‖ * ‖q.coeff j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Polynomial.sum_def, length_monomial, norm_mul] using
        length_sum_le q.support (fun j ↦ monomial (i + j) (p.coeff i * q.coeff j))
    _ = _ := by
      simp only [length, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

lemma length_one : length 1 = 1 := by
  simpa using length_monomial 0 1

lemma length_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    length (∏ i ∈ s, f i) ≤ ∏ i ∈ s, length (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [length_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (length_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (length_nonneg _))

lemma norm_coeff_le_length (p : ℤ[X]) (k : ℕ) : ‖p.coeff k‖ ≤ length p := by
  by_cases hk : k ∈ p.support
  · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hk
  · simp only [(Polynomial.notMem_support_iff.mp hk), norm_zero]
    exact length_nonneg p

lemma length_le_of_coeff_le (p : ℤ[X]) (H : ℝ) (hH : ∀ k, ‖p.coeff k‖ ≤ H) :
    length p ≤ (p.natDegree + 1 : ℝ) * H := by
  rw [length_eq_sum_range p (p.natDegree + 1) (by omega)]
  calc
    _ ≤ ∑ _k ∈ Finset.range (p.natDegree + 1), H := Finset.sum_le_sum fun k _ ↦ hH k
    _ = _ := by simp

lemma length_sign_smul (u : ℤˣ) (p : ℤ[X]) : length (u • p) = length p := by
  rw [length_eq_sum_range _ (p.natDegree + 1) ((natDegree_smul_le _ _).trans_lt (Nat.lt_succ_self _)),
    length_eq_sum_range p (p.natDegree + 1) (by omega)]
  congr 1
  ext k
  simp

lemma length_det_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ[X]) (B : ℝ)
    (_hB : 0 ≤ B) (hM : ∀ i j, length (M i j) ≤ B) :
    length M.det ≤ (Nat.factorial d : ℝ) * B ^ d := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), length (Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      length_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), B ^ d := by
      apply Finset.sum_le_sum
      intro σ _
      rw [length_sign_smul]
      exact (length_prod_le _ _).trans (by
        simpa using Finset.prod_le_prod (s := Finset.univ)
          (fun i _ ↦ length_nonneg (M (σ i) i)) (fun i _ ↦ hM _ _))
    _ = _ := by simp [Fintype.card_perm]

lemma natDegree_det_le {d D : ℕ} (M : Matrix (Fin d) (Fin d) ℤ[X])
    (hM : ∀ i j, (M i j).natDegree ≤ D) : M.det.natDegree ≤ d * D := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hM (σ i) i)

end TranscendenceTheory.IntegralNorm

open Polynomial Matrix Module
open scoped Polynomial

namespace TranscendenceTheory.IntegralNorm

lemma norm_aeval_le_length (θ : ℂ) (p : ℤ[X]) (D : ℕ) (hD : p.natDegree ≤ D) :
    ‖aeval θ p‖ ≤ length p * max 1 ‖θ‖ ^ D := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [zsmul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖(p.coeff k : ℂ) * θ ^ k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * max 1 ‖θ‖ ^ D := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul, norm_pow]
      rw [Complex.norm_intCast, Int.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg θ) (le_max_right 1 ‖θ‖) k).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖θ‖) (by have := Finset.mem_range.mp hk; omega))
    _ = _ := by rw [← Finset.sum_mul, ← length_eq_sum_range p (p.natDegree + 1) (by omega)]

lemma exists_nat_bound {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ i, f i ≤ K := by
  obtain ⟨a, ha⟩ := (Set.finite_range f).bddAbove
  obtain ⟨K, hK⟩ := exists_nat_gt (max a 1)
  refine ⟨K, by exact_mod_cast (le_max_right a 1).trans hK.le, fun i ↦ ?_⟩
  exact (ha (Set.mem_range_self i)).trans ((le_max_left a 1).trans hK.le)

section Ring

variable {S : Type*} [CommRing S] [Algebra ℤ[X] S]
variable {d : ℕ} (b : Basis (Fin (d + 1)) ℤ[X] S)

lemma leftMulMatrix_eq_sum (x : S) (i j : Fin (d + 1)) :
    Algebra.leftMulMatrix b x i j =
      ∑ k, (b.repr x k) * (b.repr (b k * b j) i) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => arg 1; arg 2; arg 1; rw [← b.sum_repr x]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

lemma leftMulMatrix_degree_le (x : S) (D K : ℕ)
    (hD : ∀ i, (b.repr x i).natDegree ≤ D)
    (hK : ∀ i j k, (b.repr (b k * b j) i).natDegree ≤ K) (i j) :
    (Algebra.leftMulMatrix b x i j).natDegree ≤ D + K := by
  rw [leftMulMatrix_eq_sum]
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact natDegree_mul_le.trans (Nat.add_le_add (hD k) (hK i j k))

lemma leftMulMatrix_length_le (x : S) (H K : ℝ) (hH : 0 ≤ H)
    (hHx : ∀ i, length (b.repr x i) ≤ H)
    (hK : ∀ i j k, length (b.repr (b k * b j) i) ≤ K) (i j) :
    length (Algebra.leftMulMatrix b x i j) ≤ (d + 1) * H * K := by
  rw [leftMulMatrix_eq_sum]
  calc
    _ ≤ ∑ k, length ((b.repr x k) * (b.repr (b k * b j) i)) := length_sum_le _ _
    _ ≤ ∑ _k : Fin (d + 1), H * K := by
      apply Finset.sum_le_sum
      intro k _
      exact (length_mul_le _ _).trans
        (mul_le_mul (hHx k) (hK i j k) (length_nonneg _) hH)
    _ = _ := by simp; ring

lemma weighted_row (φ : S →+* ℂ) (θ : ℂ)
    (hφ : ∀ p : ℤ[X], φ (algebraMap ℤ[X] S p) = aeval θ p)
    (x : S) (j : Fin (d + 1)) :
    ∑ i, φ (b i) * aeval θ (Algebra.leftMulMatrix b x i j) = φ x * φ (b j) := by
  have h := congrArg φ (b.sum_repr (x * b j))
  simp only [map_sum, Algebra.smul_def, map_mul, hφ] at h
  simpa only [Algebra.leftMulMatrix_eq_repr_mul, mul_comm] using h

end Ring

lemma norm_det_le_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (B : ℝ) (hM : ∀ i j, ‖M i j‖ ≤ B) :
    ‖M.det‖ ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, B ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      simp [norm_prod]
      simpa using Finset.prod_le_prod (s := Finset.univ)
        (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hM (σ i) i)
    _ = _ := by simp [Fintype.card_perm]

lemma norm_det_updateRow_bound {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (u : Fin (d + 1) → ℂ) (B ε : ℝ) (hε : 0 ≤ ε)
    (hM : ∀ i j, ‖M i j‖ ≤ B) (hu : ∀ j, ‖u j‖ ≤ ε) :
    ‖(M.updateRow 0 u).det‖ ≤ ((d + 1).factorial : ℝ) * ε * B ^ d := by
  classical
  rw [Matrix.det_succ_row _ 0]
  calc
    _ ≤ ∑ j : Fin (d + 1),
        ‖(-1 : ℂ) ^ (0 + j : ℕ) * (M.updateRow 0 u) 0 j *
          ((M.updateRow 0 u).submatrix (0 : Fin (d + 1)).succAbove j.succAbove).det‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin (d + 1), ε * (d.factorial * B ^ d) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Matrix.updateRow_self]
      apply mul_le_mul (hu j) _ (norm_nonneg _) hε
      have heq : ∀ i k : Fin d,
          ((M.updateRow 0 u).submatrix (0 : Fin (d + 1)).succAbove j.succAbove) i k =
            M ((0 : Fin (d + 1)).succAbove i) (j.succAbove k) := by
        intro i k
        rw [Matrix.submatrix_apply, Matrix.updateRow_apply,
          if_neg (Fin.succAbove_ne (0 : Fin (d + 1)) i)]
      simpa using norm_det_le_entries
        ((M.updateRow 0 u).submatrix (0 : Fin (d + 1)).succAbove j.succAbove)
        B (fun i k ↦ by rw [heq]; exact hM _ _)
    _ = _ := by simp [Nat.factorial_succ]; ring

section Norm

variable {S : Type*} [CommRing S] [Algebra ℤ[X] S]
variable {d : ℕ} (b : Basis (Fin (d + 1)) ℤ[X] S)

lemma norm_polynomial_bounds (φ : S →+* ℂ) (θ : ℂ)
    (hφ : ∀ p : ℤ[X], φ (algebraMap ℤ[X] S p) = aeval θ p)
    (hb : b 0 = 1) (x : S) (D K : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hD : ∀ i, (b.repr x i).natDegree ≤ D)
    (hHx : ∀ i, length (b.repr x i) ≤ H)
    (hKd : ∀ i j k, (b.repr (b k * b j) i).natDegree ≤ K)
    (hKl : ∀ i j k, length (b.repr (b k * b j) i) ≤ K)
    (hKb : ∀ i, ‖φ (b i)‖ ≤ K) :
    let p := Algebra.norm ℤ[X] x
    p.natDegree ≤ (d + 1) * (D + K) ∧
    length p ≤ ((d + 1).factorial : ℝ) * ((d + 1) * H * K) ^ (d + 1) ∧
    ‖aeval θ p‖ ≤ ((d + 1).factorial : ℝ) * (‖φ x‖ * K) *
      ((d + 1) * H * K * max 1 ‖θ‖ ^ (D + K)) ^ d := by
  classical
  dsimp only
  rw [Algebra.norm_eq_matrix_det b]
  have hdeg := leftMulMatrix_degree_le b x D K hD hKd
  have hlen := leftMulMatrix_length_le b x H K hH hHx hKl
  refine ⟨natDegree_det_le _ hdeg, length_det_le _ _ (by positivity) hlen, ?_⟩
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    (Algebra.leftMulMatrix b x).map (aeval θ)
  have hdet : M.det = aeval θ (Algebra.leftMulMatrix b x).det := by
    exact (aeval θ : ℤ[X] →ₐ[ℤ] ℂ).toRingHom.map_det _ |>.symm
  rw [← hdet]
  have hrow : (∑ i, φ (b i) • M i) = fun j ↦ φ x * φ (b j) := by
    ext j
    simpa [M] using weighted_row b φ θ hφ x j
  have heq := Matrix.det_updateRow_sum M 0 (fun i ↦ φ (b i))
  rw [hrow, hb, map_one, one_smul] at heq
  rw [← heq]
  apply norm_det_updateRow_bound _ _ _ _ (by positivity)
  · intro i j
    exact (norm_aeval_le_length θ _ (D + K) (hdeg i j)).trans
      (mul_le_mul_of_nonneg_right (hlen i j) (by positivity))
  · intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hKb j) (norm_nonneg _)

end Norm
end TranscendenceTheory.IntegralNorm

open Filter

namespace TranscendenceTheory.IntegralNorm

lemma constant_le_exp_linear (a n : ℝ) (ha : 0 ≤ a) (hn : 1 ≤ n) :
    a ≤ Real.exp (a * n) := by
  calc
    a ≤ a + 1 := by linarith
    _ ≤ Real.exp a := Real.add_one_le_exp a
    _ ≤ Real.exp (a * n) := Real.exp_le_exp.mpr (le_mul_of_one_le_right ha hn)

lemma pow_le_exp_linear (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    R ^ m ≤ Real.exp (R * m) := by
  calc
    R ^ m ≤ (Real.exp R) ^ m := pow_le_pow_left₀ hR (by linarith [Real.add_one_le_exp R]) m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma exists_norm_envelope (d : ℕ) (C R : ℝ) (K : ℕ)
    (hC : 0 < C) (hR : 1 ≤ R) (hK : 1 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N D : ℕ), 1 ≤ N → (D : ℝ) ≤ C * N →
      ((d + 1) * (D + K) : ℕ) ≤ A * N ∧
      ((d + 1).factorial : ℝ) *
          ((d + 1) * Real.exp (2 * C * N) * K) ^ (d + 1) ≤ Real.exp (A * N) ∧
      ((d + 1).factorial : ℝ) * K *
          ((d + 1) * Real.exp (2 * C * N) * K * R ^ (D + K)) ^ d ≤
        Real.exp (A * N) := by
  let F : ℝ := (d + 1).factorial
  let E : ℝ := 2 * C + (d + 1) * K + R * (C + K) + F * K + F + 1
  let A : ℝ := (d + 1) * (C + K) + (d + 2) * E + 1
  have hF : 0 ≤ F := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hR0 : 0 ≤ R := by linarith
  have hRC : 0 ≤ R * (C + K) := by positivity
  have hFK : 0 ≤ F * K := by positivity
  have hB : 0 ≤ (d + 1 : ℝ) * K := by positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hFE : F ≤ E := by dsimp [E]; linarith
  have hFKE : F * K ≤ E := by dsimp [E]; linarith
  have hBE : (d + 1 : ℝ) * K + 2 * C ≤ E := by dsimp [E]; linarith
  have hBRE : (d + 1 : ℝ) * K + 2 * C + R * (C + K) ≤ E := by dsimp [E]; linarith
  have hbase : 0 ≤ (d + 1 : ℝ) * (C + K) := by positivity
  have hEA : (d + 2 : ℝ) * E ≤ A := by dsimp [A]; linarith
  have hdegA : (d + 1 : ℝ) * (C + K) ≤ A := by
    have : 0 ≤ (d + 2 : ℝ) * E := by positivity
    dsimp [A]; linarith
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro N D hN hD
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hDK : (D + K : ℕ) ≤ (C + K) * (N : ℝ) := by
    push_cast
    nlinarith
  have hbound : (d + 1 : ℝ) * Real.exp (2 * C * N) * K ≤ Real.exp (E * N) := by
    calc
      _ = ((d + 1 : ℝ) * K) * Real.exp (2 * C * N) := by ring
      _ ≤ Real.exp (((d + 1 : ℝ) * K) * N) * Real.exp (2 * C * N) :=
        mul_le_mul_of_nonneg_right (constant_le_exp_linear _ _ hB hN') (Real.exp_pos _).le
      _ = Real.exp ((((d + 1 : ℝ) * K) + 2 * C) * N) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBE hN0)
  have hboundR : (d + 1 : ℝ) * Real.exp (2 * C * N) * K * R ^ (D + K) ≤
      Real.exp (E * N) := by
    have hpow : R ^ (D + K) ≤ Real.exp (R * (C + K) * N) := by
      refine (pow_le_exp_linear R hR0 _).trans (Real.exp_le_exp.mpr ?_)
      nlinarith [mul_le_mul_of_nonneg_left hDK hR0]
    calc
      _ = ((d + 1 : ℝ) * K) * Real.exp (2 * C * N) * R ^ (D + K) := by ring
      _ ≤ Real.exp (((d + 1 : ℝ) * K) * N) * Real.exp (2 * C * N) *
          Real.exp (R * (C + K) * N) := by gcongr; exact constant_le_exp_linear _ _ hB hN'
      _ = Real.exp ((((d + 1 : ℝ) * K) + 2 * C + R * (C + K)) * N) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBRE hN0)
  have hconst : F ≤ Real.exp (E * N) :=
    (constant_le_exp_linear F N hF hN').trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hFE hN0))
  have hconstK : F * K ≤ Real.exp (E * N) :=
    (constant_le_exp_linear (F * K) N hFK hN').trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hFKE hN0))
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (d + 1 : ℝ) * ((D + K : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (d + 1 : ℝ) * ((C + K) * N) := mul_le_mul_of_nonneg_left hDK (by positivity)
      _ = ((d + 1 : ℝ) * (C + K)) * N := by ring
      _ ≤ A * N := mul_le_mul_of_nonneg_right hdegA hN0
  · calc
      _ ≤ Real.exp (E * N) * (Real.exp (E * N)) ^ (d + 1) := by
        apply mul_le_mul hconst
        · exact pow_le_pow_left₀ (by positivity) hbound _
        · positivity
        · positivity
      _ = Real.exp ((d + 2 : ℝ) * E * N) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEA hN0)
  · calc
      _ ≤ Real.exp (E * N) * (Real.exp (E * N)) ^ d := by
        apply mul_le_mul hconstK
        · exact pow_le_pow_left₀ (by positivity) hboundR _
        · positivity
        · positivity
      _ = Real.exp ((d + 1 : ℝ) * E * N) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by nlinarith : (d + 1 : ℝ) * E ≤ A) hN0)

lemma eventually_small_after_norm (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) * Real.exp (A * N) ≤
        Real.exp (-10 * (A * N) ^ 2) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop ((10 * A ^ 2 + A) / c)),
    eventually_ge_atTop 1] with N hlogN hN
  rw [← Real.exp_add, Real.exp_le_exp]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogc : 10 * A ^ 2 + A ≤ c * Real.log N := by
    have := (div_le_iff₀ hc).mp hlogN
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hlogc (sq_nonneg (N : ℝ))
  have hlin : A * N ≤ A * (N : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : (N : ℝ) ≤ (N : ℝ) ^ 2) hA.le
  nlinarith

end TranscendenceTheory.IntegralNorm

open Polynomial Module Filter
open scoped Polynomial

namespace TranscendenceTheory.IntegralNorm

theorem small_polynomials_of_small_integral_elements
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℤ[X] S]
    (θ : ℂ) (hθ : Transcendental ℤ θ)
    (φ : S →+* ℂ)
    (hφ : ∀ p : ℤ[X], φ (algebraMap ℤ[X] S p) = aeval θ p)
    (d : ℕ) (b : Basis (Fin (d + 1)) ℤ[X] S) (hb : b 0 = 1)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
      (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
      (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
      ‖φ x‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X], (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖aeval θ p‖ ∧ ‖aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by
  classical
  obtain ⟨K, hK, hKb⟩ := exists_nat_bound
    (fun t : Fin (d + 1) × Fin (d + 1) × Fin (d + 1) ↦
      ((b.repr (b t.2.2 * b t.2.1) t.1).natDegree : ℝ) +
        length (b.repr (b t.2.2 * b t.2.1) t.1) + ‖φ (b t.1)‖)
  have hKd : ∀ i j k, (b.repr (b k * b j) i).natDegree ≤ K := by
    intro i j k
    have h := hKb (i, j, k)
    have hd : ((b.repr (b k * b j) i).natDegree : ℝ) ≤ K := by
      linarith [length_nonneg (b.repr (b k * b j) i), norm_nonneg (φ (b i))]
    exact_mod_cast hd
  have hKl : ∀ i j k, length (b.repr (b k * b j) i) ≤ K := by
    intro i j k
    have h := hKb (i, j, k)
    have hd : (0 : ℝ) ≤ (b.repr (b k * b j) i).natDegree := by positivity
    linarith [norm_nonneg (φ (b i))]
  have hKb' : ∀ i, ‖φ (b i)‖ ≤ K := by
    intro i
    have h := hKb (i, 0, 0)
    have hd : (0 : ℝ) ≤ (b.repr (b 0 * b 0) i).natDegree := by positivity
    linarith [length_nonneg (b.repr (b 0 * b 0) i)]
  obtain ⟨A, hA, henv⟩ := exists_norm_envelope d C (max 1 ‖θ‖) K hC (le_max_left _ _) hK
  have hevent : ∀ᶠ N : ℕ in atTop, ∃ p : ℤ[X],
      (p.natDegree : ℝ) ≤ A * N ∧
      (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      0 < ‖aeval θ p‖ ∧ ‖aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by
    filter_upwards [hsmall, eventually_ge_atTop 1, eventually_small_after_norm A c hA hc]
      with N hx hN hsmallN
    obtain ⟨x, hx0, hxD, hxH, hxsmall⟩ := hx
    let D := ⌊C * N⌋₊
    have hD : (D : ℝ) ≤ C * N := Nat.floor_le (by positivity)
    have hxD' : ∀ i, (b.repr x i).natDegree ≤ D := fun i ↦ Nat.le_floor (hxD i)
    have hxL : ∀ i, length (b.repr x i) ≤ Real.exp (2 * C * N) := by
      intro i
      calc
        _ ≤ ((b.repr x i).natDegree + 1 : ℝ) * Real.exp (C * N) :=
          length_le_of_coeff_le _ _ (fun k ↦ by simpa [Int.norm_eq_abs] using hxH i k)
        _ ≤ (C * N + 1) * Real.exp (C * N) :=
          mul_le_mul_of_nonneg_right (add_le_add_left (hxD i) 1) (Real.exp_pos _).le
        _ ≤ Real.exp (C * N) * Real.exp (C * N) :=
          mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hbounds := norm_polynomial_bounds b φ θ hφ hb x D K
      (Real.exp (2 * C * N)) (Real.exp_pos _).le hxD' hxL hKd hKl hKb'
    have henvN := henv N D hN hD
    let p := Algebra.norm ℤ[X] x
    have hp : p ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis b).mpr hx0
    have hpθ : aeval θ p ≠ 0 := fun h ↦ hp ((transcendental_iff.mp hθ) p h)
    refine ⟨p, ?_, ?_, norm_pos_iff.mpr hpθ, ?_⟩
    · exact (Nat.cast_le.mpr hbounds.1).trans henvN.1
    · intro k
      have hk : |(p.coeff k : ℝ)| ≤ length p := by
        simpa [Int.norm_eq_abs] using norm_coeff_le_length p k
      exact hk.trans (hbounds.2.1.trans henvN.2.1)
    · calc
        _ ≤ ((d + 1).factorial : ℝ) * (‖φ x‖ * K) *
            ((d + 1) * Real.exp (2 * C * N) * K * max 1 ‖θ‖ ^ (D + K)) ^ d := hbounds.2.2
        _ = ‖φ x‖ * (((d + 1).factorial : ℝ) * K *
            ((d + 1) * Real.exp (2 * C * N) * K * max 1 ‖θ‖ ^ (D + K)) ^ d) := by ring
        _ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) * Real.exp (A * N) :=
          mul_le_mul hxsmall henvN.2.2 (by positivity) (Real.exp_pos _).le
        _ ≤ _ := hsmallN
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨A, hA, N₀, hN₀⟩

end TranscendenceTheory.IntegralNorm

theorem solution
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℤ[X] S]
    (θ : ℂ) (hθ : Transcendental ℤ θ)
    (φ : S →+* ℂ)
    (hφ : ∀ p : ℤ[X], φ (algebraMap ℤ[X] S p) = aeval θ p)
    (d : ℕ) (b : Basis (Fin (d + 1)) ℤ[X] S) (hb : b 0 = 1)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
      (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
      (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
      ‖φ x‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X], (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖aeval θ p‖ ∧ ‖aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by
  exact TranscendenceTheory.IntegralNorm.small_polynomials_of_small_integral_elements
    θ hθ φ hφ d b hb C c hC hc hsmall
