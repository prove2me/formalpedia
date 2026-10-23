-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.reducedPhaseCovariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:15:50.953541+00:00
-- url     : https://prove2.me/submissions/721fcde9-1efd-40a6-8053-74e436b577d8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_reduced_apply {I A : Type*} [Fintype I] [Fintype A] (u : Op (I × A)) (a : Op A)
    (x : Op I) (i j : I) :
    reduced u a x i j = ∑ k, ∑ q, ∑ p, u (i, k) p * (x p.1 q.1 * a p.2 q.2) * conj (u (j, k) q) := by
  unfold reduced
  congr 1; funext k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.of_apply, Finset.sum_mul]
  rfl

theorem X7_comm_entry {J : Type*} [Fintype J] [DecidableEq J] (u : Op J) (E : J → ℝ)
    (h : Commute u (Matrix.diagonal fun p => (E p : ℂ))) (p q : J) (hpq : u p q ≠ 0) :
    E p = E q := by
  have := congrFun (congrFun h.eq p) q
  simp [Matrix.mul_apply, Matrix.diagonal_apply] at this
  have h2 : u p q * ((E q : ℂ) - E p) = 0 := by linear_combination this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hpq
  · have : ((E q - E p : ℝ) : ℂ) = 0 := by push_cast; exact h3
    have := Complex.ofReal_eq_zero.mp this
    linarith

theorem X7_evol_comm {J : Type*} [Fintype J] [DecidableEq J] (h M : Op J) (hc : Commute h M)
    (t : ℝ) : Commute (evolution h t) M := by
  unfold evolution
  exact (hc.smul_left _).exp_left

theorem X7_freq (c : ℝ) (h : ∀ φ : ℝ, Complex.exp (Complex.I * ((φ * c : ℝ) : ℂ)) = 1) : c = 0 := by
  by_contra hc
  have := h (Real.pi / c)
  rw [show Real.pi / c * c = Real.pi by field_simp, mul_comm, Complex.exp_pi_mul_I] at this
  norm_num at this

theorem X7_ee (a b : ℝ) :
    Complex.exp (Complex.I * (a : ℂ)) * conj (Complex.exp (Complex.I * (b : ℂ))) =
      Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal]; ring

theorem X7_evol_diag {J : Type*} [Fintype J] [DecidableEq J] (z : J → ℝ) (φ : ℝ) :
    evolution (Matrix.diagonal fun i => (z i : ℂ)) φ =
      Matrix.diagonal fun i => Complex.exp (Complex.I * ((-(φ * z i) : ℝ) : ℂ)) := by
  unfold evolution
  have hs : ((-(φ : ℂ) * Complex.I) • Matrix.diagonal fun i => (z i : ℂ)) =
      Matrix.diagonal fun i => (-(φ : ℂ) * Complex.I) * (z i : ℂ) := by
    ext i j; simp [Matrix.diagonal_apply]
  rw [hs, Matrix.exp_diagonal, Pi.exp_def]
  congr 1; funext i; rw [← Complex.exp_eq_exp_ℂ]; congr 1; push_cast; ring

theorem X7_dconj {J : Type*} [Fintype J] [DecidableEq J] (v : J → ℂ) (x : Op J) (i j : J) :
    (Matrix.diagonal v * x * (Matrix.diagonal v).conjTranspose) i j = v i * x i j * conj (v j) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]; rfl

theorem X7_kron_dd {I A : Type*} [DecidableEq I] [DecidableEq A] (f : I → ℂ) (g : A → ℂ) :
    Matrix.kronecker (Matrix.diagonal f) (Matrix.diagonal g) =
      Matrix.diagonal fun p => f p.1 * g p.2 :=
  Matrix.diagonal_kronecker_diagonal f g

theorem X7_u_energy {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (u : Op (I × A)) (zS : I → ℝ) (zA : A → ℝ)
    (hsym : ∀ phi : ℝ, Commute u (Matrix.kronecker
      (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi) (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi)))
    (p q : I × A) (hpq : u p q ≠ 0) : zS p.1 + zA p.2 = zS q.1 + zA q.2 := by
  have : zS q.1 + zA q.2 - (zS p.1 + zA p.2) = 0 := by
    apply X7_freq
    intro φ
    have hc := hsym φ
    rw [X7_evol_diag, X7_evol_diag, X7_kron_dd] at hc
    have := congrFun (congrFun hc.eq p) q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h2 : u p q * (Complex.exp (Complex.I * ((-(φ * zS q.1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((-(φ * zA q.2) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((-(φ * zS p.1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((-(φ * zA p.2) : ℝ) : ℂ))) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hpq
    have h4 : Complex.exp (Complex.I * ((-(φ * zS q.1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((-(φ * zA q.2) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((-(φ * zS p.1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((-(φ * zA p.2) : ℝ) : ℂ)) := by linear_combination h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    have h5 := congrArg (fun w => w * Complex.exp (-(Complex.I * ((-(φ * zS q.1) : ℝ) : ℂ) +
      Complex.I * ((-(φ * zA q.2) : ℝ) : ℂ)))) h4
    simp only [← Complex.exp_add] at h5
    rw [add_neg_cancel, Complex.exp_zero] at h5
    rw [h5]; congr 1; push_cast; ring
  linarith

theorem X7_a_energy {A : Type*} [Fintype A] [DecidableEq A] (zA : A → ℝ) (a : Op A)
    (hinv : ∀ phi : ℝ, evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi * a *
      (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi).conjTranspose = a)
    (k l : A) (hkl : a k l ≠ 0) : zA k = zA l := by
  have : zA l - zA k = 0 := by
    apply X7_freq
    intro φ
    have := congrFun (congrFun (hinv φ) k) l
    rw [X7_evol_diag, X7_dconj] at this
    have h2 : a k l * (Complex.exp (Complex.I * ((-(φ * zA k) : ℝ) : ℂ)) *
        conj (Complex.exp (Complex.I * ((-(φ * zA l) : ℝ) : ℂ))) - 1) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hkl
    rw [X7_ee] at h3
    rw [← sub_eq_zero.mp h3]; congr 1; push_cast; ring
  linarith

theorem X7_offdiag {I : Type*} [DecidableEq I] (x : Op I) (hx : diagonal x = x) (i j : I)
    (hij : i ≠ j) : x i j = 0 := by
  have := congrFun (congrFun hx i) j
  simp [diagonal, hij] at this; exact this.symm

theorem X7_ondiag {I : Type*} [DecidableEq I] (x : Op I) (hx : diagonal x = 0) (i : I) :
    x i i = 0 := by
  have := congrFun (congrFun hx i) i
  simpa [diagonal] using this

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (u : Op (I × A)) (hu : u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1)
    (zS : I → ℝ) (zA : A → ℝ) (a : Op A) (ha : IsDensityMatrix a)
    (hsym : ∀ phi : ℝ, Commute u (Matrix.kronecker
      (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi) (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi)))
    (hinv : ∀ phi : ℝ, evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi * a *
      (evolution (Matrix.diagonal fun i => (zA i : ℂ)) phi).conjTranspose = a) :
    (∀ (phi : ℝ) (x : Op I),
      reduced u a (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi * x *
        (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi).conjTranspose) =
      evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi * reduced u a x *
        (evolution (Matrix.diagonal fun i => (zS i : ℂ)) phi).conjTranspose) ∧
    Commute a (Matrix.diagonal fun i => (zA i : ℂ)) ∧
    (Function.Injective zA → diagonal a = a) ∧
    (Function.Injective zS → Decoupled (reduced u a)) := by
  have ku := X7_u_energy u zS zA hsym
  have ka := X7_a_energy zA a hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ x
    ext i j
    rw [X7_evol_diag]
    simp only [X7_dconj, X7_reduced_apply]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    rcases eq_or_ne (u (i, k) p) 0 with h1 | h1
    · simp [h1]
    rcases eq_or_ne (u (j, k) q) 0 with h2 | h2
    · simp [h2]
    rcases eq_or_ne (a p.2 q.2) 0 with h4 | h4
    · simp [h4]
    have e1 := ku _ _ h1
    have e2 := ku _ _ h2
    have e4 := ka _ _ h4
    simp only at e1 e2
    have hv : Complex.exp (Complex.I * ((-(φ * zS p.1) : ℝ) : ℂ)) *
        conj (Complex.exp (Complex.I * ((-(φ * zS q.1) : ℝ) : ℂ))) =
        Complex.exp (Complex.I * ((-(φ * zS i) : ℝ) : ℂ)) *
        conj (Complex.exp (Complex.I * ((-(φ * zS j) : ℝ) : ℂ))) := by
      rw [X7_ee, X7_ee]; congr 2
      have : zS p.1 - zS q.1 = zS i - zS j := by linarith
      push_cast
      have hc : ((zS p.1 : ℂ) - zS q.1) = zS i - zS j := by exact_mod_cast this
      linear_combination (-(φ : ℂ)) * hc
    linear_combination (u (i, k) p * x p.1 q.1 * a p.2 q.2 * conj (u (j, k) q)) * hv
  · ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases eq_or_ne (a k l) 0 with h | h
    · simp [h]
    · rw [ka k l h, mul_comm]
  · intro hA
    ext k l
    by_cases hkl : k = l
    · subst hkl; simp [diagonal]
    · simp only [diagonal, hkl, if_false]
      by_contra h
      exact hkl (hA (ka k l (Ne.symm h)))
  · intro hz
    constructor
    · intro x hx
      have kx : ∀ i j, x i j ≠ 0 → i = j := by
        intro i j h; by_contra hij; exact h (X7_offdiag x hx i j hij)
      ext i j
      by_cases hij : i = j
      · subst hij; simp [diagonal]
      · simp only [diagonal, hij, if_false]
        rw [X7_reduced_apply]; symm
        apply Finset.sum_eq_zero; intro k _
        apply Finset.sum_eq_zero; intro q _
        apply Finset.sum_eq_zero; intro p _
        rcases eq_or_ne (u (i, k) p) 0 with h1 | h1
        · simp [h1]
        rcases eq_or_ne (u (j, k) q) 0 with h2 | h2
        · simp [h2]
        rcases eq_or_ne (x p.1 q.1) 0 with h3 | h3
        · simp [h3]
        rcases eq_or_ne (a p.2 q.2) 0 with h4 | h4
        · simp [h4]
        exfalso
        have e1 := ku _ _ h1
        have e2 := ku _ _ h2
        have e3 := kx _ _ h3
        have e4 := ka _ _ h4
        simp only at e1 e2
        rw [e3] at e1
        exact hij (hz (by linarith))
    · intro x hx
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [diagonal, if_true, Matrix.zero_apply]
        rw [X7_reduced_apply]
        apply Finset.sum_eq_zero; intro k _
        apply Finset.sum_eq_zero; intro q _
        apply Finset.sum_eq_zero; intro p _
        rcases eq_or_ne (u (i, k) p) 0 with h1 | h1
        · simp [h1]
        rcases eq_or_ne (u (i, k) q) 0 with h2 | h2
        · simp [h2]
        rcases eq_or_ne (a p.2 q.2) 0 with h4 | h4
        · simp [h4]
        have e1 := ku _ _ h1
        have e2 := ku _ _ h2
        have e4 := ka _ _ h4
        simp only at e1 e2
        have : p.1 = q.1 := hz (by linarith)
        rw [this, X7_ondiag x hx]; simp
      · simp [diagonal, hij]
