-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.localGeneratorSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:06:54.713645+00:00
-- url     : https://prove2.me/submissions/f5f96459-9b12-42e0-981b-3f0f2668004e

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

/-- X ⊗ 1 has evolution -1 at time π. -/
def X7_V : Op (Bool × Bool) := fun p q => if p.2 = q.2 then (if p.1 && q.1 then (-1 : ℂ) else 1) else 0
def X7_Vi : Op (Bool × Bool) := fun p q => if p.2 = q.2 then (if p.1 && q.1 then (-1 / 2 : ℂ) else 1 / 2) else 0
def X7_g : Op (Bool × Bool) := Matrix.kronecker pauliX 1
def X7_dg : Bool × Bool → ℂ := fun p => (-(Real.pi : ℂ) * Complex.I) * (if p.1 then -1 else 1)

theorem X7_VVi : X7_V * X7_Vi = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_Vi, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply] <;> norm_num

theorem X7_ViV : X7_Vi * X7_V = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_Vi, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply] <;> norm_num

theorem X7_g_gen : (-((Real.pi : ℝ) : ℂ) * Complex.I) • X7_g = X7_V * Matrix.diagonal X7_dg * X7_Vi := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_V, X7_Vi, X7_g, X7_dg, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, QAlgorithms.pauliX, Matrix.diagonal_apply] <;> ring

theorem X7_g_evol : evolution X7_g Real.pi = -1 := by
  unfold evolution
  rw [X7_g_gen]
  let u : (Op (Bool × Bool))ˣ := ⟨X7_V, X7_Vi, X7_VVi, X7_ViV⟩
  have h := Matrix.exp_units_conj u (Matrix.diagonal X7_dg)
  simp only [u, Units.inv_mk] at h
  rw [h, Matrix.exp_diagonal]
  have hd : NormedSpace.exp X7_dg = fun _ => -1 := by
    funext p
    rw [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
    simp only [X7_dg]
    split_ifs
    · rw [show -(Real.pi : ℂ) * Complex.I * -1 = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
    · rw [show -(Real.pi : ℂ) * Complex.I * 1 = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]; norm_num
  rw [hd, show (Matrix.diagonal fun _ => (-1 : ℂ)) = -1 by
    ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;> simp]
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, X7_VVi]

theorem X7_g_herm : X7_g.IsHermitian := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [X7_g, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, QAlgorithms.pauliX]

theorem X7_g_decoupled (b : Op Bool) (hb : b.trace = 1) :
    Decoupled (reduced (evolution X7_g Real.pi) b) := by
  have hid : ∀ x, reduced (evolution X7_g Real.pi) b x = x := by
    intro x
    rw [X7_g_evol]
    ext i j
    simp only [reduced, Matrix.conjTranspose_neg, Matrix.conjTranspose_one, Matrix.neg_mul,
      Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.of_apply]
    rw [← Finset.mul_sum]
    have : ∑ k, b k k = 1 := hb
    rw [this, mul_one]
  constructor
  · intro x hx; rw [hid, hx]
  · intro x hx; rw [hid, hx]

open ComplexOrder in
theorem X7_rho10_density : IsDensityMatrix (rho 1 0) := by
  have he : rho 1 0 = Matrix.diagonal (fun i : Bool => if i then (0 : ℂ) else 1) := by
    ext i j; cases i <;> cases j <;> simp [rho, Matrix.diagonal]
  refine ⟨?_, ?_⟩
  · rw [he]
    exact (Matrix.posSemidef_diagonal_iff).mpr (by intro i; cases i <;> simp)
  · simp [rho, Matrix.trace]

theorem X7_rho10_diag : diagonal (rho 1 0) = rho 1 0 := by
  ext i j; cases i <;> cases j <;> simp [diagonal, rho]

theorem X7_kron_diag_one {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (f : I → ℂ) : Matrix.kronecker (Matrix.diagonal f) (1 : Op A) = Matrix.diagonal fun p => f p.1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h1 : i = j <;> by_cases h2 : k = l <;> simp [h1, h2]

theorem X7_offdiag {I : Type*} [DecidableEq I] (x : Op I) (hx : diagonal x = x) (i j : I)
    (hij : i ≠ j) : x i j = 0 := by
  have := congrFun (congrFun hx i) j
  simp [diagonal, hij] at this; exact this.symm

theorem X7_ondiag {I : Type*} [DecidableEq I] (x : Op I) (hx : diagonal x = 0) (i : I) :
    x i i = 0 := by
  have := congrFun (congrFun hx i) i
  simpa [diagonal] using this

theorem X7_local_dec {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (u : Op (I × A)) (z : I → ℝ) (hz : Function.Injective z)
    (hc : Commute u (Matrix.diagonal fun p => ((z p.1 : ℝ) : ℂ))) (a : Op A) :
    Decoupled (reduced u a) := by
  have key : ∀ p q, u p q ≠ 0 → p.1 = q.1 := fun p q h =>
    hz (X7_comm_entry u (fun p => z p.1) hc p q h)
  constructor
  · intro x hx
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
      have e1 := key _ _ h1
      have e2 := key _ _ h2
      simp only at e1 e2
      rw [← e1, ← e2, X7_offdiag x hx i j hij]; simp
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
      have e1 := key _ _ h1
      have e2 := key _ _ h2
      simp only at e1 e2
      rw [← e1, ← e2, X7_ondiag x hx i]; simp
    · simp [diagonal, hij]

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (h : Op (I × A)) (hh : h.IsHermitian) (z : I → ℝ) (hz : Function.Injective z)
    (a : Op A) (ha : IsDensityMatrix a) (tau : ℝ) (ht : 0 < tau)
    (hcomm : Commute h (Matrix.kronecker (Matrix.diagonal fun i => (z i : ℂ)) (1 : Op A))) :
    Decoupled (reduced (evolution h tau) a) ∧
    (∃ (g : Op (Bool × Bool)) (b : Op Bool) (t : ℝ), g.IsHermitian ∧
      IsDensityMatrix b ∧ 0 < t ∧
      ¬Commute g (Matrix.kronecker pauliZ (1 : Op Bool)) ∧
      Decoupled (reduced (evolution g t) b)) := by
  refine ⟨?_, X7_g, rho 1 0, Real.pi, X7_g_herm, X7_rho10_density, Real.pi_pos, ?_,
    X7_g_decoupled _ X7_rho10_density.2⟩
  · rw [X7_kron_diag_one] at hcomm
    exact X7_local_dec _ z hz (X7_evol_comm _ _ hcomm tau) a
  · intro hc
    have := congrFun (congrFun hc.eq (false, false)) (true, false)
    simp [X7_g, QAlgorithms.pauliX, QAlgorithms.pauliZ, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply] at this
    norm_num at this
