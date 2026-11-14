-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nuclear_norm_ls_frobenius_oracle_bound
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:48:58.137291+00:00
-- url     : https://prove2.me/submissions/ac4d1b42-e875-4d32-b442-f49327a76122

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective

open Matrix
open WainwrightHDS.NucNorm

namespace NucNormCounterexample

/-! ### Part 1: Trace inner product, Frobenius norm, spectral norm, and nuclear norm helpers -/

private lemma frobSq_eq_traceInner {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq A = traceInner A A := by
  simp [frobSq, traceInner, sq]

private lemma traceInner_self_nonneg {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 ≤ traceInner A A := by
  rw [← frobSq_eq_traceInner]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma traceInner_comm {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = traceInner B A := by
  simp only [traceInner, mul_comm]

private lemma traceInner_add_left {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  simp only [traceInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private lemma traceInner_add_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  simp only [traceInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private lemma traceInner_sub_left {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (A - B) C = traceInner A C - traceInner B C := by
  simp only [traceInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma traceInner_sub_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B - C) = traceInner A B - traceInner A C := by
  simp only [traceInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma traceInner_smul_left {d₁ d₂ : ℕ} (c : ℝ) (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (c • A) B = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma traceInner_smul_right {d₁ d₂ : ℕ} (c : ℝ) (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (c • B) = c * traceInner A B := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

private lemma traceInner_neg_left {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (-A) B = -traceInner A B := by
  simp only [traceInner, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

private lemma traceInner_diag {n : ℕ} (a b : Fin n → ℝ) :
    traceInner (diagonal a) (diagonal b) = ∑ i, a i * b i := by
  simp [traceInner, Matrix.diagonal_apply]

private lemma traceInner_cs_sq {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B ^ 2 ≤ traceInner A A * traceInner B B := by
  simpa [traceInner, Fintype.sum_prod_type, sq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun ij : Fin m × Fin n => A ij.1 ij.2)
      (fun ij : Fin m × Fin n => B ij.1 ij.2))

private lemma traceInner_sum_obsOp {n d₁ d₂ : ℕ} (Xs : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ)
    (u : Fin n → ℝ) (a : ℝ) (D : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (a • ∑ i, u i • Xs i) D = a * ∑ i, u i * obsOp Xs D i := by
  rw [traceInner_smul_left]
  congr 1
  unfold obsOp
  calc traceInner (∑ i, u i • Xs i) D
      = ∑ x, ∑ y, ∑ i, u i * (Xs i x y * D x y) := by
        simp only [traceInner, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
          mul_assoc]
    _ = ∑ x, ∑ i, ∑ y, u i * (Xs i x y * D x y) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, u i * (Xs i x y * D x y) := Finset.sum_comm
    _ = ∑ i, u i * traceInner (Xs i) D := by
        simp only [traceInner, Finset.mul_sum]

private lemma traceInner_eq_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = (A.transpose * B).trace := by
  dsimp [traceInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

private lemma toEuclideanLin_mul {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

private lemma toEuclideanLin_transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    Matrix.toEuclideanLin A.transpose = (Matrix.toEuclideanLin A).adjoint := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

private lemma trace_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun n ℝ).toBasis

private lemma traceInner_eq_linearMap_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂))
      ((Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin B)) := by
  rw [traceInner_eq_trace, ← trace_toEuclideanLin, toEuclideanLin_mul, toEuclideanLin_transpose]

private lemma euclideanSpace_inner_eq {n : Type*} [Fintype n] (x y : EuclideanSpace ℝ n) :
    @inner ℝ (EuclideanSpace ℝ n) _ x y = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

private lemma toEuclideanLin_apply_apply {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ)
    (v : EuclideanSpace ℝ (Fin d₂)) (i : Fin d₁) :
    Matrix.toEuclideanLin M v i = ∑ j, M i j * v j :=
  rfl

private lemma norm_toEuclideanLin_apply_eigenvectorBasis {d₁ d₂ : ℕ}
    (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂) :
    ‖Matrix.toEuclideanLin M
      (((Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self).eigenvectorBasis
        (by simp [finrank_euclideanSpace] : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂) i)‖ =
      (Matrix.toEuclideanLin M).singularValues i := by
  set T := Matrix.toEuclideanLin M
  set S := T.adjoint ∘ₗ T
  set hS := T.isSymmetric_adjoint_comp_self
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set v := hS.eigenvectorBasis hn i
  have h_inner_sq : ‖T v‖ ^ 2 = @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (T v) (T v) := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq]
  have h_adj : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (T v) (T v) =
      @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v (S v) := by
    rw [real_inner_comm (T v) (T v)]
    exact (LinearMap.adjoint_inner_right T v (T v)).symm
  have h_eig : S v = (hS.eigenvalues hn i) • v := hS.apply_eigenvectorBasis hn i
  have h_inner_v : @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v (S v) = hS.eigenvalues hn i := by
    rw [h_eig, inner_smul_right, real_inner_self_eq_norm_mul_norm,
      (hS.eigenvectorBasis hn).orthonormal.1 i, mul_one, mul_one]
  have h_sq_sing : T.singularValues i ^ 2 = hS.eigenvalues hn i := T.sq_singularValues_fin hn i
  have h_norm_sq : ‖T v‖ ^ 2 = T.singularValues i ^ 2 := by
    rw [h_inner_sq, h_adj, h_inner_v, ← h_sq_sing]
  have h_sqrt := congr_arg Real.sqrt h_norm_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (T.singularValues_nonneg i)] at h_sqrt

private lemma finrank_range_toEuclideanLin_le_min {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ min d₁ d₂ := by
  have h1 : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ d₁ := by
    have h := Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin M))
    simpa [finrank_euclideanSpace] using h
  have h2 : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ d₂ := by
    have h := LinearMap.finrank_range_le (Matrix.toEuclideanLin M)
    simpa [finrank_euclideanSpace] using h
  exact le_min h1 h2

private lemma sum_singularValues_eq_nucNorm {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∑ i : Fin d₂, (Matrix.toEuclideanLin M).singularValues i = nucNorm M := by
  dsimp [nucNorm, singVal]
  rw [Fin.sum_univ_eq_sum_range]
  have h_min_le : min d₁ d₂ ≤ d₂ := min_le_right d₁ d₂
  rw [← Finset.sum_range_add_sum_Ico _ h_min_le]
  have h_zero : ∑ i ∈ Finset.Ico (min d₁ d₂) d₂, (Matrix.toEuclideanLin M).singularValues i = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    exact (Matrix.toEuclideanLin M).singularValues_eq_zero_iff_le_finrank_range.mpr
      ((finrank_range_toEuclideanLin_le_min M).trans hx.1)
  rw [h_zero, add_zero]

private lemma nucNorm_nonneg {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 ≤ nucNorm M :=
  Finset.sum_nonneg fun j _ => (Matrix.toEuclideanLin M).singularValues_nonneg j

private lemma traceInner_le_nucNorm_mul_opNorm2 {d₁ d₂ : ℕ} (M N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner M N ≤ nucNorm M * opNorm2 N := by
  set TM := Matrix.toEuclideanLin M
  set TN := Matrix.toEuclideanLin N
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  have h_trace : traceInner M N =
      ∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i)) := by
    rw [traceInner_eq_linearMap_trace M N, LinearMap.trace_eq_sum_inner (TM.adjoint.comp TN) b]
    exact Fintype.sum_congr _ _ fun i => LinearMap.adjoint_inner_right TM (b i) (TN (b i))
  have h_term_le : ∀ i : Fin d₂,
      @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i)) ≤
        TM.singularValues i * opNorm2 N := by
    intro i
    have h_cs := real_inner_le_norm (TM (b i)) (TN (b i))
    rw [norm_toEuclideanLin_apply_eigenvectorBasis M i] at h_cs
    have h_norm_TN : ‖TN (b i)‖ ≤ opNorm2 N := by
      dsimp [opNorm2]
      have h := ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap TN) (b i)
      rwa [b.orthonormal.1 i, mul_one] at h
    exact h_cs.trans (mul_le_mul_of_nonneg_left h_norm_TN (TM.singularValues_nonneg i))
  calc traceInner M N
      = ∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i)) := h_trace
    _ ≤ ∑ i : Fin d₂, TM.singularValues i * opNorm2 N := Finset.sum_le_sum fun i _ => h_term_le i
    _ = nucNorm M * opNorm2 N := by rw [← Finset.sum_mul, sum_singularValues_eq_nucNorm M]

private lemma traceInner_le_opNorm2_mul_nucNorm {d₁ d₂ : ℕ} (G A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner G A ≤ opNorm2 G * nucNorm A := by
  rw [traceInner_comm, mul_comm]
  exact traceInner_le_nucNorm_mul_opNorm2 A G

private lemma opNorm2_diagonal_le {n : ℕ} (d : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ i, |d i| ≤ c) : opNorm2 (diagonal d) ≤ c := by
  dsimp [opNorm2]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  change ‖Matrix.toEuclideanLin (diagonal d) x‖ ≤ c * ‖x‖
  set y := Matrix.toEuclideanLin (diagonal d) x
  have hy_coord : ∀ i : Fin n, y i = d i * x i := by
    intro i
    rw [toEuclideanLin_apply_apply]
    simp [Matrix.diagonal_apply]
  have hy_sq : ‖y‖ ^ 2 = ∑ i : Fin n, (d i * x i) ^ 2 := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm, euclideanSpace_inner_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy_coord i, sq]
  have hx_sq : ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm, euclideanSpace_inner_eq]
    refine Finset.sum_congr rfl fun i _ => by rw [sq]
  have hsq : ‖y‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, hy_sq, hx_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_pow]
    have hd2 : d i ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs (d i), ← sq_abs c, abs_of_nonneg hc]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd i) 2
    exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg y), Real.sqrt_sq (mul_nonneg hc (norm_nonneg x))] at hsqrt

private lemma nucNorm_diagonal_of_nonneg {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 ≤ d k) :
    nucNorm (diagonal d) = ∑ k, d k := by
  set M := diagonal d
  set TM := Matrix.toEuclideanLin M
  have hTM_adj : TM.adjoint = TM := by
    change (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin M
    rw [← toEuclideanLin_transpose]
    simp [M, Matrix.diagonal_transpose]
  have hTM_psd : ∀ u : EuclideanSpace ℝ (Fin n),
      0 ≤ @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u (TM u) := by
    intro u
    rw [euclideanSpace_inner_eq]
    refine Finset.sum_nonneg fun k _ => ?_
    have hk : TM u k = d k * u k := by
      rw [toEuclideanLin_apply_apply]
      simp [M, Matrix.diagonal_apply]
    rw [hk, show u k * (d k * u k) = d k * (u k ^ 2) by ring]
    exact mul_nonneg (hd k) (sq_nonneg _)
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  set hS := TM.isSymmetric_adjoint_comp_self
  set b := hS.eigenvectorBasis hn
  have h_each : ∀ i : Fin n,
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b i) (TM (b i)) = TM.singularValues i := by
    intro i
    set v := b i
    set σ := TM.singularValues i
    have hσ0 : 0 ≤ σ := TM.singularValues_nonneg i
    have hv1 : ‖v‖ = 1 := b.orthonormal.1 i
    have hTv_norm : ‖TM v‖ = σ := norm_toEuclideanLin_apply_eigenvectorBasis M i
    have hS_eig : (TM.adjoint ∘ₗ TM) v = (σ ^ 2) • v := by
      rw [TM.sq_singularValues_fin hn i]
      exact hS.apply_eigenvectorBasis hn i
    have hTM2 : TM (TM v) = (σ ^ 2) • v := by
      simpa [LinearMap.comp_apply, hTM_adj] using hS_eig
    by_cases hσ : σ = 0
    · have h0 : TM v = 0 := norm_eq_zero.mp (hTv_norm.trans hσ)
      rw [h0, hσ, inner_zero_right]
    · have hσpos : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
      set u := TM v - σ • v
      have hu_eq : TM u + σ • u = 0 := by
        simp only [u, map_sub, map_smul, smul_sub, smul_smul, ← sq, hTM2]
        abel
      have h_orth : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u (TM u) +
          σ * @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u u = 0 := by
        have h0 : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u (TM u + σ • u) = 0 := by
          rw [hu_eq, inner_zero_right]
        rwa [inner_add_right, inner_smul_right] at h0
      have hu_nonneg : 0 ≤ @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u u := real_inner_self_nonneg
      have hu_zero : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ u u = 0 := by
        nlinarith [hTM_psd u]
      have hu0 : u = 0 := inner_self_eq_zero.mp hu_zero
      have hTv_eq : TM v = σ • v := sub_eq_zero.mp hu0
      rw [hTv_eq, inner_smul_right, real_inner_self_eq_norm_mul_norm, hv1, mul_one, mul_one]
  rw [← sum_singularValues_eq_nucNorm M]
  change ∑ i : Fin n, TM.singularValues i = ∑ k, d k
  simp_rw [← h_each]
  rw [← LinearMap.trace_eq_sum_inner TM b, trace_toEuclideanLin M]
  simp [M, Matrix.trace_diagonal]

private lemma norm_toEuclideanLin_le_singVal_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin M x‖ ≤ singVal 0 M * ‖x‖ := by
  set TM := Matrix.toEuclideanLin M
  set S := TM.adjoint ∘ₗ TM
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  set hS := TM.isSymmetric_adjoint_comp_self
  set b := hS.eigenvectorBasis hn
  have h1 : ‖TM x‖ ^ 2 = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (S x) := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm, real_inner_comm (TM x) (TM x)]
    exact (LinearMap.adjoint_inner_right TM x (TM x)).symm
  have h2 : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (S x) =
      ∑ i : Fin n, (TM.singularValues i ^ 2) *
        (@inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (b i)) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (S x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsym : @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b i) (S x) =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (S (b i)) x := (hS (b i) x).symm
    have heig : S (b i) = (TM.singularValues i ^ 2) • b i := by
      rw [TM.sq_singularValues_fin hn i]
      exact hS.apply_eigenvectorBasis hn i
    rw [hsym, heig, real_inner_comm x (TM.singularValues i ^ 2 • b i), inner_smul_right]
    ring
  have h3 : ∑ i : Fin n, (TM.singularValues i ^ 2) *
        (@inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (b i)) ^ 2 ≤
      (TM.singularValues 0 ^ 2) * ∑ i : Fin n,
        (@inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (b i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hanti : TM.singularValues i ≤ TM.singularValues 0 :=
      TM.singularValues_antitone (Nat.zero_le i)
    have hsq_le : TM.singularValues i ^ 2 ≤ TM.singularValues 0 ^ 2 :=
      pow_le_pow_left₀ (TM.singularValues_nonneg i) hanti 2
    exact mul_le_mul_of_nonneg_right hsq_le (sq_nonneg _)
  have h4 : ∑ i : Fin n, (@inner ℝ (EuclideanSpace ℝ (Fin n)) _ x (b i)) ^ 2 = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_left x
  have hsq : ‖TM x‖ ^ 2 ≤ (singVal 0 M * ‖x‖) ^ 2 := by
    dsimp [singVal]
    rw [mul_pow, h1, h2, ← h4]
    exact h3
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hs0 : 0 ≤ singVal 0 M := (Matrix.toEuclideanLin M).singularValues_nonneg 0
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hs0 (norm_nonneg x))] at hsqrt

/-! ### Part 2: Counterexample data (`d₁ = d₂ = 101`, `N = 10202`, `r = 1`) -/

noncomputable section

def blocks (a b c : ℝ) (i : Fin 101) : ℝ :=
  if i.val = 0 then a else if i.val ≤ 50 then b else c

lemma sum_blocks (a b c : ℝ) : ∑ i, blocks a b c i = a + 50 * b + 50 * c := by
  rw [Fin.sum_univ_succ]
  have h1 : ∀ i : Fin 50, blocks a b c ((Fin.castAdd 50 i : Fin 100).succ) = b := by
    intro i; dsimp [blocks]; split_ifs <;> first | rfl | omega
  have h2 : ∀ i : Fin 50, blocks a b c ((Fin.natAdd 50 i : Fin 100).succ) = c := by
    intro i; dsimp [blocks]; split_ifs <;> first | rfl | omega
  rw [Fin.sum_univ_add (fun i : Fin (50 + 50) => blocks a b c i.succ)]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [blocks]
  ring

lemma blocks_mul (a b c x y z : ℝ) :
    (fun i => blocks a b c i * blocks x y z i) = blocks (a * x) (b * y) (c * z) := by
  funext i; dsimp [blocks]; split_ifs <;> rfl

lemma blocks_sub (a b c x y z : ℝ) :
    (fun i => blocks a b c i - blocks x y z i) = blocks (a - x) (b - y) (c - z) := by
  funext i; dsimp [blocks]; split_ifs <;> rfl

abbrev Mat := Matrix (Fin 101) (Fin 101) ℝ

def Theta : Mat := diagonal (blocks 2 (2 / 25) 0)
def Hat : Mat := diagonal (blocks 1 0 (7 / 25))
def D : Mat := diagonal (blocks (-1) (-2 / 25) (7 / 25))
def S : Mat := diagonal (blocks (-1) (-1) 1)
def Z : Mat := diagonal (blocks (-3 / 200) (-3 / 200) (-1 / 200))
def G : Mat := (1 / 200 : ℝ) • S

lemma D_eq : D = Hat - Theta := by
  unfold D Hat Theta
  rw [diagonal_sub, blocks_sub]
  norm_num

lemma Z_eq : Z = G - (1 / 100 : ℝ) • (1 : Mat) := by
  ext i j
  simp only [Z, G, S, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst j; dsimp [blocks]; split_ifs <;> norm_num
  · simp [h]

lemma D_sq : traceInner D D = 131 / 25 := by
  rw [D, traceInner_diag, blocks_mul, sum_blocks]; norm_num

lemma DS : traceInner D S = 19 := by
  rw [D, S, traceInner_diag, blocks_mul, sum_blocks]; norm_num

lemma DZ : traceInner D Z = 1 / 200 := by
  rw [D, Z, traceInner_diag, blocks_mul, sum_blocks]; norm_num

lemma S_op : opNorm2 S ≤ 1 := by
  refine opNorm2_diagonal_le _ 1 zero_le_one fun i => ?_
  dsimp [blocks]; split_ifs <;> norm_num

lemma negS_op : opNorm2 (-S) ≤ 1 := by
  have hneg : -S = diagonal (blocks 1 1 (-1)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp only [S, Matrix.neg_apply, Matrix.diagonal_apply_eq]; dsimp [blocks]; split_ifs <;> norm_num
    · simp [S, hij]
  rw [hneg]
  refine opNorm2_diagonal_le _ 1 zero_le_one fun i => ?_
  dsimp [blocks]; split_ifs <;> norm_num

lemma one_op : opNorm2 (1 : Mat) ≤ 1 := by
  have hone : (1 : Mat) = diagonal (fun _ => 1) := (Matrix.diagonal_one).symm
  rw [hone]
  exact opNorm2_diagonal_le _ 1 zero_le_one fun _ => by norm_num

lemma G_op : opNorm2 G ≤ (1 / 100 : ℝ) / 2 := by
  have hG : G = diagonal (blocks (-1 / 200) (-1 / 200) (1 / 200)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp only [G, S, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq]
      dsimp [blocks]; split_ifs <;> norm_num
    · simp [G, S, hij]
  rw [hG]
  refine opNorm2_diagonal_le _ ((1 / 100 : ℝ) / 2) (by norm_num) fun i => ?_
  dsimp [blocks]; split_ifs <;> norm_num

lemma Theta_nuc : nucNorm Theta = 6 := by
  rw [Theta, nucNorm_diagonal_of_nonneg]
  · rw [sum_blocks]; norm_num
  · intro i; dsimp [blocks]; split_ifs <;> norm_num

lemma Hat_nuc : nucNorm Hat = 15 := by
  rw [Hat, nucNorm_diagonal_of_nonneg]
  · rw [sum_blocks]; norm_num
  · intro i; dsimp [blocks]; split_ifs <;> norm_num

lemma I_Hat : traceInner (1 : Mat) Hat = nucNorm Hat := by
  rw [Hat_nuc]
  have hid : (1 : Mat) = diagonal (blocks 1 1 1) := by
    ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply, blocks]
  rw [hid, Hat, traceInner_diag, blocks_mul, sum_blocks]; norm_num

lemma first_singular : 2 ≤ singVal 0 Theta := by
  let e0 : EuclideanSpace ℝ (Fin 101) := WithLp.toLp 2 (Pi.single (0 : Fin 101) (1 : ℝ))
  have he0_norm : ‖e0‖ = 1 := by
    have hsq : ‖e0‖ ^ 2 = 1 := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, euclideanSpace_inner_eq]
      simp [e0, Pi.single_apply, mul_ite]
    have hs := congr_arg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg e0), Real.sqrt_one] at hs
  have hTe0_ge : 2 ≤ ‖Matrix.toEuclideanLin Theta e0‖ := by
    set y := Matrix.toEuclideanLin Theta e0
    have hy0 : y 0 = 2 := by
      rw [toEuclideanLin_apply_apply]
      simp [Theta, e0, Matrix.diagonal_apply, Pi.single_apply, blocks]
    have hsq : (2 : ℝ) ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [sq (‖y‖), ← real_inner_self_eq_norm_mul_norm, euclideanSpace_inner_eq]
      have hterm : (2 : ℝ) ^ 2 ≤ ∑ i : Fin 101, y i * y i := by
        have h0 : (2 : ℝ) ^ 2 = y 0 * y 0 := by rw [hy0]; ring
        rw [h0]
        exact Finset.single_le_sum (fun i _ => mul_self_nonneg (y i)) (Finset.mem_univ 0)
      exact hterm
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg y)] at hs
  have hbound := norm_toEuclideanLin_le_singVal_zero Theta e0
  rw [he0_norm, mul_one] at hbound
  exact hTe0_ge.trans hbound

lemma tail_bounds :
    0 ≤ ∑ j ∈ Finset.Ico 1 (min 101 101), singVal j Theta ∧
      ∑ j ∈ Finset.Ico 1 (min 101 101), singVal j Theta ≤ 4 := by
  have hmin : min 101 101 = 101 := by norm_num
  rw [hmin]
  refine ⟨Finset.sum_nonneg fun j _ => (Matrix.toEuclideanLin Theta).singularValues_nonneg j, ?_⟩
  have hsplit : Finset.range 101 = insert 0 (Finset.Ico 1 101) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnuc : nucNorm Theta = singVal 0 Theta + ∑ j ∈ Finset.Ico 1 101, singVal j Theta := by
    dsimp [nucNorm]
    rw [hmin, hsplit, Finset.sum_insert (by simp)]
  linarith [Theta_nuc, first_singular]

/-! ### Part 3: Quadratic form geometry and RSC verification -/

def U : Mat := (2 : ℝ) • Z + (19 / 32 : ℝ) • S

lemma U_sq : traceInner U U = 23603501 / 640000 := by
  have he : U = diagonal (blocks (-499 / 800) (-499 / 800) (467 / 800)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp only [U, Z, S, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq]
      dsimp [blocks]; split_ifs <;> norm_num
    · simp [U, Z, S, h]
  rw [he, traceInner_diag, blocks_mul, sum_blocks]; norm_num

def Pproj (A : Mat) : Mat := A - (traceInner D A / (131 / 25)) • D
def Hmat (A : Mat) : Mat := (200 * traceInner Z A) • Z + (200 : ℝ) • Pproj A
def energy (A : Mat) : ℝ := 200 * traceInner Z A ^ 2 + 200 * traceInner (Pproj A) (Pproj A)

lemma P_orth (A : Mat) : traceInner D (Pproj A) = 0 := by
  rw [Pproj, traceInner_sub_right, traceInner_smul_right, D_sq]; ring

lemma P_selfadj (A B : Mat) : traceInner (Pproj A) B = traceInner A (Pproj B) := by
  rw [Pproj, Pproj, traceInner_sub_left, traceInner_sub_right,
    traceInner_smul_left, traceInner_smul_right, traceInner_comm A D]
  ring

lemma P_idem (A : Mat) : Pproj (Pproj A) = Pproj A := by rw [Pproj, P_orth]; simp
lemma P_D : Pproj D = 0 := by rw [Pproj, D_sq]; norm_num

lemma P_smul (a : ℝ) (A : Mat) : Pproj (a • A) = a • Pproj A := by
  unfold Pproj
  rw [traceInner_smul_right]
  simp only [smul_sub, smul_smul]
  congr 1; congr 1; ring

lemma P_add (A B : Mat) : Pproj (A + B) = Pproj A + Pproj B := by
  unfold Pproj
  rw [traceInner_add_right, add_div, add_smul]
  abel

lemma H_D : Hmat D = Z := by
  rw [Hmat, P_D, traceInner_comm Z D, DZ]; norm_num

lemma inner_H (A B : Mat) : traceInner (Hmat A) B =
    200 * traceInner Z A * traceInner Z B + 200 * traceInner (Pproj A) (Pproj B) := by
  rw [Hmat, traceInner_add_left, traceInner_smul_left, traceInner_smul_left]
  have he : traceInner (Pproj A) B = traceInner (Pproj A) (Pproj B) := by
    rw [P_selfadj, P_selfadj, P_idem]
  rw [he]

lemma energy_eq (A : Mat) : energy A = traceInner (Hmat A) A := by
  rw [inner_H]; unfold energy; ring

lemma energy_rsc (A : Mat) :
    frobSq A - nucNorm A ^ 2 / 64 ≤ energy A := by
  let a : ℝ := traceInner D A / (131 / 25)
  let V : Mat := Pproj A
  have hDV : traceInner D V = 0 := P_orth A
  have he : A = a • D + V := by dsimp [a, V, Pproj]; abel
  have hAA : traceInner A A = a ^ 2 * (131 / 25) + traceInner V V := by
    conv_lhs => rw [he]
    rw [traceInner_add_left, traceInner_add_right, traceInner_add_right,
      traceInner_smul_left, traceInner_smul_left, traceInner_smul_right,
      traceInner_smul_right, D_sq, hDV, traceInner_comm V D, hDV]
    ring
  have hZA : traceInner Z A = a / 200 + traceInner Z V := by
    rw [he, traceInner_add_right, traceInner_smul_right, traceInner_comm Z D, DZ]; ring
  have hSA : traceInner S A = 19 * a + traceInner S V := by
    rw [he, traceInner_add_right, traceInner_smul_right, traceInner_comm S D, DS]; ring
  have hUV : traceInner U V = 2 * traceInner Z V + 19 / 32 * traceInner S V := by
    rw [U, traceInner_add_left, traceInner_smul_left, traceInner_smul_left]
  have hcs := traceInner_cs_sq U V
  rw [U_sq] at hcs
  have hv := traceInner_self_nonneg V
  have hbound : traceInner A A - traceInner S A ^ 2 / 64 ≤ energy A := by
    rw [hAA, hSA, energy, hZA]
    change a ^ 2 * (131 / 25) + traceInner V V - (19 * a + traceInner S V) ^ 2 / 64 ≤
      200 * (a / 200 + traceInner Z V) ^ 2 + 200 * traceInner V V
    have hy := sq_nonneg (a / 2 + traceInner U V)
    rw [hUV] at hy hcs
    nlinarith [hy, sq_nonneg (traceInner Z V), sq_nonneg (traceInner S V), sq_nonneg a]
  have hs : traceInner S A ≤ nucNorm A := by
    have h1 := traceInner_le_opNorm2_mul_nucNorm S A
    nlinarith [S_op, nucNorm_nonneg A]
  have hns : -traceInner S A ≤ nucNorm A := by
    have h1 := traceInner_le_opNorm2_mul_nucNorm (-S) A
    rw [traceInner_neg_left] at h1
    nlinarith [negS_op, nucNorm_nonneg A]
  have hsq : traceInner S A ^ 2 ≤ nucNorm A ^ 2 := by nlinarith [nucNorm_nonneg A]
  rw [frobSq_eq_traceInner]
  linarith

def beta : ℝ := traceInner D G / (1 / 200)
def Vnoise : Mat := (1 / 200 : ℝ) • (G - beta • Z)
def alpha : ℝ := beta - traceInner Z Vnoise / (1 / 200)
def W : Mat := alpha • D + Vnoise

lemma Vnoise_orth : traceInner D Vnoise = 0 := by
  rw [Vnoise, traceInner_smul_right, traceInner_sub_right, traceInner_smul_right, DZ]
  unfold beta; ring

lemma P_W : Pproj W = Vnoise := by
  rw [W, P_add, P_smul, P_D]
  have h : Pproj Vnoise = Vnoise := by rw [Pproj, Vnoise_orth]; simp
  rw [h]; simp

lemma H_W : Hmat W = G := by
  rw [Hmat, P_W, W, traceInner_add_right, traceInner_smul_right, traceInner_comm Z D, DZ]
  unfold alpha Vnoise
  ext i j; simp; ring

/-! ### Part 4: Observation ensemble (`N = 10202`) and optimality of `Hat` -/

abbrev Ix := Fin 1 ⊕ (Fin 101 × Fin 101)
def N : ℕ := 10202

def idxEquiv : Ix ≃ Fin N :=
  ((Equiv.refl (Fin 1)).sumCongr finProdFinEquiv).trans finSumFinEquiv

def basis (ij : Fin 101 × Fin 101) : Mat :=
  vecMulVec (Pi.single ij.1 1) (Pi.single ij.2 1)

lemma basis_ti (ij : Fin 101 × Fin 101) (A : Mat) : traceInner (basis ij) A = A ij.1 ij.2 := by
  simp [basis, traceInner, Matrix.vecMulVec_apply, Pi.single_apply, ite_mul, mul_ite]

lemma ti_ext (A B : Mat) (h : ∀ C : Mat, traceInner A C = traceInner B C) : A = B := by
  ext i j
  have he := h (basis (i, j))
  rw [traceInner_comm A, traceInner_comm B, basis_ti, basis_ti] at he
  exact he

def scale : ℝ := Real.sqrt (200 * (N : ℝ))
def raw : Ix → Mat := Sum.elim (fun _ => scale • Z) (fun ij => scale • Pproj (basis ij))
def Xs (i : Fin N) : Mat := raw (idxEquiv.symm i)

lemma N_val : N = 10202 := rfl
lemma N_pos : 0 < (N : ℝ) := by rw [N_val]; norm_num

lemma scale_sq : scale ^ 2 = 200 * (N : ℝ) :=
  Real.sq_sqrt (by positivity [N_pos])

lemma raw_gram (A B : Mat) :
    ∑ j : Ix, traceInner (raw j) A * traceInner (raw j) B =
      scale ^ 2 * (traceInner Z A * traceInner Z B + traceInner (Pproj A) (Pproj B)) := by
  have hproj : ∀ ij, traceInner (Pproj (basis ij)) A = Pproj A ij.1 ij.2 := by
    intro ij; rw [P_selfadj, basis_ti]
  have hprojB : ∀ ij, traceInner (Pproj (basis ij)) B = Pproj B ij.1 ij.2 := by
    intro ij; rw [P_selfadj, basis_ti]
  simp only [raw, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    traceInner_smul_left, Fin.sum_univ_one, hproj, hprojB]
  have he : ∑ ij : Fin 101 × Fin 101,
      scale * Pproj A ij.1 ij.2 * (scale * Pproj B ij.1 ij.2) =
        scale ^ 2 * traceInner (Pproj A) (Pproj B) := by
    simp only [traceInner, Fintype.sum_prod_type, Finset.mul_sum]
    congr 1; funext i; congr 1; funext j; ring
  rw [he]; ring

lemma gram (A B : Mat) :
    traceInner ((1 / (N : ℝ)) • ∑ i, obsOp Xs A i • Xs i) B = traceInner (Hmat A) B := by
  rw [traceInner_sum_obsOp]
  unfold obsOp
  have he : (∑ i : Fin N, traceInner (Xs i) A * traceInner (Xs i) B) =
      ∑ j : Ix, traceInner (raw j) A * traceInner (raw j) B := by
    simpa only [Xs] using (Equiv.sum_comp idxEquiv.symm
      (fun j : Ix => traceInner (raw j) A * traceInner (raw j) B))
  rw [he, raw_gram, scale_sq, inner_H]
  have hn := ne_of_gt N_pos
  field_simp [hn]

lemma gram_matrix (A : Mat) :
    (1 / (N : ℝ)) • ∑ i, obsOp Xs A i • Xs i = Hmat A :=
  ti_ext _ _ (gram A)

lemma prediction_energy (A : Mat) :
    (∑ i, (obsOp Xs A i) ^ 2) / (N : ℝ) = energy A := by
  have he := gram A A
  rw [traceInner_sum_obsOp, ← energy_eq] at he
  simpa only [sq, div_eq_mul_inv, one_div, mul_comm, mul_one] using he

def noise : Fin N → ℝ := obsOp Xs W
def yObs : Fin N → ℝ := fun i => obsOp Xs Theta i + noise i

lemma noise_adj : (1 / (N : ℝ)) • ∑ i, noise i • Xs i = G := by
  rw [noise, gram_matrix, H_W]

lemma rsc_holds (A : Mat) :
    1 / (2 * (N : ℝ)) * ∑ i, (obsOp Xs A i) ^ 2 ≥
      (1 : ℝ) / 2 * frobSq A - ((N : ℝ) / (128 * 202)) * (((101 : ℝ) + 101) / (N : ℝ)) * nucNorm A ^ 2 := by
  have he := prediction_energy A
  have hb := energy_rsc A
  have hn := ne_of_gt N_pos
  have e1 : 1 / (2 * (N : ℝ)) * ∑ i, (obsOp Xs A i) ^ 2 = energy A / 2 := by
    rw [← he]; field_simp [hn]
  have e2 : ((N : ℝ) / (128 * 202)) * (((101 : ℝ) + 101) / (N : ℝ)) = 1 / 128 := by
    field_simp [hn]; norm_num
  change _ ≤ _
  rw [e1, e2]
  linarith

lemma noise_good : opNorm2 ((1 / (N : ℝ)) • ∑ i, noise i • Xs i) ≤ (1 / 100 : ℝ) / 2 := by
  rw [noise_adj]; exact G_op

lemma optimal (T : Mat) :
    lsNucObjective Xs yObs (1 / 100) Hat ≤ lsNucObjective Xs yObs (1 / 100) T := by
  let E : Mat := T - Hat
  let residual : Fin N → ℝ := fun i => yObs i - obsOp Xs Hat i
  have hres : ∀ i, residual i = noise i - obsOp Xs D i := by
    intro i
    dsimp [residual, yObs, obsOp]
    rw [D_eq, traceInner_sub_right]; ring
  have hcand : ∀ i, yObs i - obsOp Xs T i = residual i - obsOp Xs E i := by
    intro i
    dsimp [residual, E, obsOp]
    rw [traceInner_sub_right]; ring
  have hinner : 1 / (N : ℝ) * ∑ i, residual i * obsOp Xs E i =
      1 / 100 * traceInner (1 : Mat) E := by
    have hnoise := traceInner_sum_obsOp Xs noise (1 / (N : ℝ)) E
    rw [noise_adj] at hnoise
    have hd := gram D E
    rw [H_D, traceInner_sum_obsOp] at hd
    have he : G - Z = (1 / 100 : ℝ) • (1 : Mat) := by rw [Z_eq]; abel
    have hdiff := traceInner_sub_left G Z E
    rw [he, traceInner_smul_left] at hdiff
    simp only [hres, sub_mul, Finset.sum_sub_distrib]
    nlinarith
  have hsupport : traceInner (1 : Mat) T ≤ nucNorm T := by
    have h1 := traceInner_le_opNorm2_mul_nucNorm (1 : Mat) T
    nlinarith [one_op, nucNorm_nonneg T]
  have hE : traceInner (1 : Mat) E = traceInner (1 : Mat) T - nucNorm Hat := by
    dsimp only [E]
    rw [traceInner_sub_right, I_Hat]
  rw [hE] at hinner
  have hexp : ∑ i, (residual i - obsOp Xs E i) ^ 2 =
      ∑ i, residual i ^ 2 - 2 * ∑ i, residual i * obsOp Xs E i + ∑ i, (obsOp Xs E i) ^ 2 := by
    have hpoint : ∀ i, (residual i - obsOp Xs E i) ^ 2 =
        residual i ^ 2 - 2 * (residual i * obsOp Xs E i) + (obsOp Xs E i) ^ 2 := fun _ => by ring
    simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2c : 2 * (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) := by field_simp
  rw [← h2c] at hinner
  have hS : 0 ≤ ∑ i : Fin N, (obsOp Xs E i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (obsOp Xs E i)
  have hc : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num) N_pos.le)
  have hnonneg := mul_nonneg hc hS
  dsimp [lsNucObjective]
  change 1 / (2 * (N : ℝ)) * ∑ i, residual i ^ 2 + 1 / 100 * nucNorm Hat ≤ _
  simp only [hcand]
  rw [hexp]
  nlinarith

lemma conclusion_fails :
    ¬ frobSq (Hat - Theta) ≤
      9 / 2 * ((1 / 100 : ℝ) ^ 2 / (1 : ℝ) ^ 2) * (1 : ℕ) +
        1 / (1 : ℝ) * (2 * (1 / 100 : ℝ) * ∑ j ∈ Finset.Ico 1 (min 101 101), singVal j Theta +
          32 * ((N : ℝ) / (128 * 202)) * ((101 : ℝ) + 101) / (N : ℝ) *
            (∑ j ∈ Finset.Ico 1 (min 101 101), singVal j Theta) ^ 2) := by
  rw [← D_eq, frobSq_eq_traceInner, D_sq]
  have he : 32 * ((N : ℝ) / (128 * 202)) * ((101 : ℝ) + 101) / (N : ℝ) = 1 / 4 := by
    have hn := ne_of_gt N_pos
    field_simp [hn]; norm_num
  rw [he]
  norm_num
  obtain ⟨ht0, ht4⟩ := tail_bounds
  have ht2 : (∑ j ∈ Finset.Ico 1 (min 101 101), singVal j Theta) ^ 2 ≤ 16 := by nlinarith
  have hmin : min 101 101 = 101 := by norm_num
  rw [hmin] at ht0 ht4 ht2
  linarith

end
end NucNormCounterexample

open NucNormCounterexample

theorem solution :
    ¬ (∀ {n d₁ d₂ : ℕ}
      (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
      (w y : Fin n → ℝ) (_hy : ∀ i, y i = obsOp X Θstar i + w i)
      (κ c₀ lam : ℝ) (_hκ : 0 < κ) (_hc₀ : 0 < c₀) (_hlam : 0 < lam)
      (_hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
        1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
          κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
      (_hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
      (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
      (_hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ,
        lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
      (r : ℕ) (_hr₁ : 1 ≤ r) (_hrd : r ≤ min d₁ d₂)
      (_hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n),
      frobSq (Θhat - Θstar) ≤
        9 / 2 * (lam ^ 2 / κ ^ 2) * r +
          1 / κ * (2 * lam * ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar +
            32 * c₀ * ((d₁ : ℝ) + d₂) / n *
              (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2)) := by
  intro hall
  have hc₀ : (0 : ℝ) < (N : ℝ) / (128 * 202) := by positivity [N_pos]
  have hrκ : 128 * ((N : ℝ) / (128 * 202)) * ((101 : ℝ) + 101) * (1 : ℕ) ≤ 1 * (N : ℝ) := by
    have hn := ne_of_gt N_pos
    field_simp [hn]; norm_num
  exact conclusion_fails (hall Xs Theta noise yObs (fun _ => rfl)
    1 ((N : ℝ) / (128 * 202)) (1 / 100)
    (by norm_num) hc₀ (by norm_num)
    rsc_holds noise_good Hat optimal
    1 (by norm_num) (by norm_num) hrκ)
