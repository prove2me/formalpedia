-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P04.optimal_complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:04:14.425844+00:00
-- url     : https://prove2.me/submissions/1a0c8b52-6664-44b7-ba65-b3c602542726

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]


section S169K
open scoped MatrixOrder

lemma S169K_core {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace.re ∧ ((P * Q).trace.re = 0 → P * Q = 0) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC hD
  set E := C * Dᴴ
  have htE : (P * Q).trace = (Eᴴ * E).trace := by
    rw [hC, hD]
    simp only [E, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by noncomm_ring, Matrix.trace_mul_comm]
    congr 1; noncomm_ring
  have hnn := (Matrix.posSemidef_conjTranspose_mul_self E).trace_nonneg
  refine ⟨by rw [htE]; exact (Complex.nonneg_iff.mp hnn).1, fun h0 => ?_⟩
  have hz : (Eᴴ * E).trace = 0 := by
    apply Complex.ext
    · rw [← htE]; simpa using h0
    · simpa using (Complex.nonneg_iff.mp hnn).2.symm
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at hz
  rw [hC, hD, show Cᴴ * C * (Dᴴ * D) = Cᴴ * (C * Dᴴ) * D by noncomm_ring]
  change Cᴴ * E * D = 0
  rw [hz]; simp

end S169K

lemma S169K_I1 (X : Matrix A A ℂ) (J : Matrix (A × B) (A × B) ℂ) :
    (Matrix.kronecker X (1 : Matrix B B ℂ) * J).trace = (X * traceRight J).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, traceRight, Matrix.of_apply, Finset.mul_sum]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma S169K_I2 (T J : Matrix (A × B) (A × B) ℂ) :
    (QAlgorithms.Entanglement.partialTransposeFirst T * J).trace =
      (T * QAlgorithms.Entanglement.partialTransposeFirst J).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.Entanglement.partialTransposeFirst,
    Matrix.of_apply, Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma S169K_I4 (T : Matrix (A × B) (A × B) ℂ) :
    (QAlgorithms.Entanglement.partialTransposeFirst T).trace = T.trace := by
  simp [Matrix.trace, QAlgorithms.Entanglement.partialTransposeFirst]

lemma S169K_I5 (R : Matrix (A × B) (A × B) ℂ) :
    (traceRight R).transpose = traceRight (QAlgorithms.Entanglement.partialTransposeFirst R) := by
  ext i j; simp [traceRight, QAlgorithms.Entanglement.partialTransposeFirst]

theorem S169K_main [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (rho xi : Matrix A A ℂ) (Lambda Theta J R : Matrix (A × B) (A × B) ℂ)
    (mu nu : ℝ) (hmin : SdpMinFeasible N epsilon rho xi Lambda Theta)
    (hmax : SdpMaxFeasible N mu nu J R)
    (hminopt : xi.trace.re = metaValue N epsilon)
    (hmaxopt : mu * (1-epsilon) - nu = metaValue N epsilon) :
    rho.trace = 1 ∧
    (Lambda * QAlgorithms.Papers.Independent.Information100.P34.choi N).trace.re = 1-epsilon ∧
    Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) * R = Lambda * R ∧
    Matrix.kronecker xi (1 : Matrix B B ℂ) * J = (Lambda + QAlgorithms.Entanglement.partialTransposeFirst Theta) * J ∧
    (nu : ℂ) • rho = traceRight (QAlgorithms.Entanglement.partialTransposeFirst R) * rho ∧
    QAlgorithms.Entanglement.partialTransposeFirst J * Theta = 0 ∧
    traceRight J * xi = xi ∧
    (mu : ℂ) • (QAlgorithms.Papers.Independent.Information100.P34.choi N * Lambda) = (J + R) * Lambda := by
  obtain ⟨⟨hρ, hρtr⟩, ⟨hΛ, hρΛ, hεΛ⟩, hξ, hΘ, hS2⟩ := hmin
  obtain ⟨hμ, hν, ⟨hJ, hJΓ, hJ1⟩, hR, hS4, hS7⟩ := hmax
  set K := QAlgorithms.Papers.Independent.Information100.P34.choi N
  set Γ := @QAlgorithms.Entanglement.partialTransposeFirst A B
  have hρT : rho.transpose.PosSemidef := hρ.transpose
  have heq : xi.trace.re = mu * (1 - epsilon) - nu := by rw [hminopt, hmaxopt]
  -- seven slacks
  have k1 := S169K_core _ _ hξ hJ1
  have k2 := S169K_core _ _ hS2 hJ
  have k3 := S169K_core _ _ hΘ hJΓ
  have k4 := S169K_core _ _ hS4 hΛ
  have k6 := S169K_core _ _ hρΛ hR
  have k7 := S169K_core _ _ hρT hS7
  have hs5 : 0 ≤ mu * ((Lambda * K).trace.re - (1 - epsilon)) :=
    mul_nonneg hμ (by linarith)
  have ident : (xi * (1 - traceRight J)).trace.re +
      ((Matrix.kronecker xi (1 : Matrix B B ℂ) - Lambda - Γ Theta) * J).trace.re +
      (Theta * Γ J).trace.re + ((J + R - (mu : ℂ) • K) * Lambda).trace.re +
      mu * ((Lambda * K).trace.re - (1 - epsilon)) +
      ((Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) - Lambda) * R).trace.re +
      (rho.transpose * ((nu : ℂ) • (1 : Matrix A A ℂ) - traceRight R)).trace.re = 0 := by
    have t1 : (xi * (1 - traceRight J)).trace = xi.trace - (xi * traceRight J).trace := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
    have t2 : ((Matrix.kronecker xi (1 : Matrix B B ℂ) - Lambda - Γ Theta) * J).trace =
        (xi * traceRight J).trace - (Lambda * J).trace - (Theta * Γ J).trace := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, S169K_I1, S169K_I2]
    have t4 : ((J + R - (mu : ℂ) • K) * Lambda).trace =
        (Lambda * J).trace + (Lambda * R).trace - (mu : ℂ) * (Lambda * K).trace := by
      rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_mul_comm J, Matrix.trace_mul_comm R, Matrix.trace_mul_comm K,
        smul_eq_mul]
    have t6 : ((Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) - Lambda) * R).trace =
        (rho.transpose * traceRight R).trace - (Lambda * R).trace := by
      rw [Matrix.sub_mul, Matrix.trace_sub, S169K_I1]
    have t7 : (rho.transpose * ((nu : ℂ) • (1 : Matrix A A ℂ) - traceRight R)).trace =
        (nu : ℂ) - (rho.transpose * traceRight R).trace := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_transpose, hρtr, smul_eq_mul, mul_one]
    rw [t1, t2, t4, t6, t7]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    linarith
  have z1 : (xi * (1 - traceRight J)).trace.re = 0 := by linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z2 : ((Matrix.kronecker xi (1 : Matrix B B ℂ) - Lambda - Γ Theta) * J).trace.re = 0 := by
    linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z3 : (Theta * Γ J).trace.re = 0 := by linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z4 : ((J + R - (mu : ℂ) • K) * Lambda).trace.re = 0 := by
    linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z5 : mu * ((Lambda * K).trace.re - (1 - epsilon)) = 0 := by
    linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z6 : ((Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) - Lambda) * R).trace.re = 0 := by
    linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  have z7 : (rho.transpose * ((nu : ℂ) • (1 : Matrix A A ℂ) - traceRight R)).trace.re = 0 := by
    linarith [k1.1, k2.1, k3.1, k4.1, k6.1, k7.1]
  -- μ > 0
  have hμpos : 0 < mu := by
    rcases eq_or_lt_of_le hμ with h0 | h0
    · exfalso
      rw [← h0] at heq
      have hxt := (S169K_core _ _ hξ Matrix.PosSemidef.one).1
      rw [Matrix.mul_one] at hxt
      have hx0 : xi = 0 := by
        have := (S169K_core _ _ hξ Matrix.PosSemidef.one).2 (by rw [Matrix.mul_one]; linarith)
        rwa [Matrix.mul_one] at this
      rw [hx0, show Matrix.kronecker (0 : Matrix A A ℂ) (1 : Matrix B B ℂ) = 0 by
        ext; simp [Matrix.kronecker]] at hS2
      have htr := (S169K_core _ _ hS2 Matrix.PosSemidef.one).1
      simp only [Matrix.mul_one, Matrix.kronecker, Matrix.kroneckerMap_zero_left, zero_sub,
        Matrix.trace_sub, Matrix.trace_neg, S169K_I4, Complex.sub_re, Complex.neg_re] at htr
      have hΓt : (Γ Theta).trace = Theta.trace := S169K_I4 Theta
      rw [hΓt] at htr
      have hΛt := (S169K_core _ _ hΛ Matrix.PosSemidef.one).1
      have hΘt := (S169K_core _ _ hΘ Matrix.PosSemidef.one).1
      rw [Matrix.mul_one] at hΛt hΘt
      have hΛ0 : Lambda = 0 := by
        have := (S169K_core _ _ hΛ Matrix.PosSemidef.one).2 (by rw [Matrix.mul_one]; linarith)
        rwa [Matrix.mul_one] at this
      rw [hΛ0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re] at hεΛ
      linarith
    · exact h0
  have zero_of {P Q : Matrix (A × B) (A × B) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
      (h : (P * Q).trace.re = 0) : P * Q = 0 := (S169K_core _ _ hP hQ).2 h
  refine ⟨hρtr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (mul_eq_zero.mp z5).resolve_left hμpos.ne'; linarith
  · have := zero_of hρΛ hR z6
    rw [Matrix.sub_mul, sub_eq_zero] at this; exact this
  · have := zero_of hS2 hJ z2
    rw [Matrix.sub_mul, Matrix.sub_mul, sub_sub, ← Matrix.add_mul, sub_eq_zero] at this; exact this
  · have := (S169K_core _ _ hρT hS7).2 z7
    have h2 := congrArg Matrix.transpose this
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, S169K_I5, Matrix.transpose_zero, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, sub_eq_zero] at h2
    exact h2
  · have := zero_of hΘ hJΓ z3
    have h2 := congrArg Matrix.conjTranspose this
    rwa [Matrix.conjTranspose_mul, hJΓ.1.eq, hΘ.1.eq, Matrix.conjTranspose_zero] at h2
  · have := (S169K_core _ _ hξ hJ1).2 z1
    have h2 := congrArg Matrix.conjTranspose this
    rw [Matrix.conjTranspose_mul, hJ1.1.eq, hξ.1.eq, Matrix.conjTranspose_zero, Matrix.sub_mul,
      Matrix.one_mul, sub_eq_zero] at h2
    exact h2.symm
  · have := zero_of hS4 hΛ z4
    rw [Matrix.sub_mul, sub_eq_zero, Matrix.smul_mul] at this; exact this.symm

end QAlgorithms.Papers.Independent.Support50.P04

end

open scoped Matrix ComplexOrder
open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P04 in
theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (rho xi : Matrix A A ℂ) (Lambda Theta J R : Matrix (A × B) (A × B) ℂ)
    (mu nu : ℝ) (hmin : SdpMinFeasible N epsilon rho xi Lambda Theta)
    (hmax : SdpMaxFeasible N mu nu J R)
    (hminopt : xi.trace.re = metaValue N epsilon)
    (hmaxopt : mu * (1-epsilon) - nu = metaValue N epsilon) :
    rho.trace = 1 ∧
    (Lambda * QAlgorithms.Papers.Independent.Information100.P34.choi N).trace.re = 1-epsilon ∧
    Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) * R = Lambda * R ∧
    Matrix.kronecker xi (1 : Matrix B B ℂ) * J = (Lambda + QAlgorithms.Entanglement.partialTransposeFirst Theta) * J ∧
    (nu : ℂ) • rho = traceRight (QAlgorithms.Entanglement.partialTransposeFirst R) * rho ∧
    QAlgorithms.Entanglement.partialTransposeFirst J * Theta = 0 ∧
    traceRight J * xi = xi ∧
    (mu : ℂ) • (QAlgorithms.Papers.Independent.Information100.P34.choi N * Lambda) = (J + R) * Lambda :=
  S169K_main N hN epsilon he0 he1 rho xi Lambda Theta J R mu nu hmin hmax hminopt hmaxopt
