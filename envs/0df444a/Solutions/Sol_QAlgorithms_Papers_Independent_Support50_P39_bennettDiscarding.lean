-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P39.bennettDiscarding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:29:16.298983+00:00
-- url     : https://prove2.me/submissions/a33784fc-3f04-48d5-a7c6-ba6fbcc5b5b0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39


namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms Matrix Polynomial

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

lemma x5bn_tr_cfc {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

lemma x5bn_sum_roots {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = ((A.charpoly.roots).map (fun z => g z.re)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

lemma x5bn_vn {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    vnEntropy A = -((A.charpoly.roots).map (fun z => z.re * Real.logb 2 z.re)).sum := by
  unfold vnEntropy
  have h := x5bn_sum_roots hA (fun x => x * Real.logb 2 x)
  try simp only at h
  rw [x5bn_tr_cfc hA, ← h, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma x5bn_tr {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = ((A.charpoly.roots).map (fun z => z.re)).sum := by
  have := x5bn_tr_cfc hA (fun x => x)
  rw [cfc_id' ℝ A] at this
  have h := x5bn_sum_roots hA (fun x => x)
  try simp only at h
  rw [this, ← h, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma x5bn_roots_prod {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    (∏ i, (X - C ((c i : ℝ) : ℂ))).roots = Multiset.map (fun i => ((c i : ℝ) : ℂ)) Finset.univ.val := by
  rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

lemma x5bn_charpoly_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A ⊗ₖ B)).charpoly =
      ∏ p : m × n, (X - C (((hA.eigenvalues p.1 * hB.eigenvalues p.2 : ℝ)) : ℂ)) := by
  set U : Matrix m m ℂ := (hA.eigenvectorUnitary : Matrix m m ℂ)
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ)
  have hA' : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hB' : B = V * diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star V := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hK : A ⊗ₖ B =
      (U ⊗ₖ V) * ((diagonal (RCLike.ofReal ∘ hA.eigenvalues)) ⊗ₖ
        (diagonal (RCLike.ofReal ∘ hB.eigenvalues))) * ((star U) ⊗ₖ (star V)) := by
    conv_lhs => rw [hA', hB', Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  rw [hK, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hUU, hVV,
    Matrix.one_kronecker_one, Matrix.one_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp

/-- additivity of von Neumann entropy for a Kronecker product of density matrices -/
lemma x5bn_vn_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) :
    vnEntropy ((A ⊗ₖ B)) = vnEntropy A + vnEntropy B := by
  have hAh := hA.1.isHermitian
  have hBh := hB.1.isHermitian
  have hKh : (A ⊗ₖ B).IsHermitian := (hA.1.kronecker hB.1).isHermitian
  rw [x5bn_vn hKh, x5bn_charpoly_kron hAh hBh, x5bn_roots_prod, x5bn_vn hAh, x5bn_vn hBh]
  have sA := x5bn_sum_roots hAh (fun x => x * Real.logb 2 x)
  have sB := x5bn_sum_roots hBh (fun x => x * Real.logb 2 x)
  try simp only at sA sB
  rw [← sA, ← sB]
  have tA := x5bn_tr hAh
  have tB := x5bn_tr hBh
  rw [hA.2] at tA; rw [hB.2] at tB
  have uA := x5bn_sum_roots hAh (fun x => x)
  have uB := x5bn_sum_roots hBh (fun x => x)
  try simp only at uA uB
  rw [← uA] at tA; rw [← uB] at tB
  simp only [Complex.one_re] at tA tB
  rw [Multiset.map_map]
  simp only [Function.comp_def, Complex.ofReal_re]
  rw [← Finset.sum_eq_multiset_sum, Fintype.sum_prod_type]
  have key : ∀ x y : ℝ, x * y * Real.logb 2 (x * y) =
      y * (x * Real.logb 2 x) + x * (y * Real.logb 2 y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [Real.logb_mul hx hy]; ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [← tB, ← Finset.sum_mul, ← tA]
  ring

end

end QAlgorithms.Papers.Independent.Support50.P39


namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms Matrix Polynomial

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

lemma x5bn_vn_reindex {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {M : Matrix m m ℂ} (hM : M.IsHermitian) :
    vnEntropy (Matrix.reindex e e M) = vnEntropy M := by
  have hR : (Matrix.reindex e e M).IsHermitian := hM.submatrix _
  rw [x5bn_vn hR, x5bn_vn hM, Matrix.charpoly_reindex]

lemma x5bn_pf_eq {T A B : Type*} (tau : Matrix T T ℂ) (sigma : Matrix (A × B) (A × B) ℂ) :
    productFactor tau sigma =
      Matrix.reindex (Equiv.prodAssoc T A B).symm (Equiv.prodAssoc T A B).symm (tau ⊗ₖ sigma) := by
  ext ⟨⟨t, a⟩, b⟩ ⟨⟨t', a'⟩, b'⟩
  rfl

lemma x5bn_vn_pf {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq T] [DecidableEq A] [DecidableEq B] [DecidableEq ((T × A) × B)]
    {tau : Matrix T T ℂ} {sigma : Matrix (A × B) (A × B) ℂ}
    (htau : IsDensityMatrix tau) (hsigma : IsDensityMatrix sigma) :
    vnEntropy (productFactor tau sigma) = vnEntropy tau + vnEntropy sigma := by
  rw [x5bn_pf_eq, x5bn_vn_reindex _ (htau.1.kronecker hsigma.1).isHermitian,
    x5bn_vn_kron htau hsigma]

lemma x5bn_tl_pf {T A B : Type*} [Fintype T] [Fintype A]
    {tau : Matrix T T ℂ} {sigma : Matrix (A × B) (A × B) ℂ} (htau : tau.trace = 1) :
    traceLeft (productFactor tau sigma) = traceLeft sigma := by
  ext b b'
  simp only [traceLeft, productFactor, Matrix.of_apply, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum]
  · simp only [Matrix.trace, Matrix.diag] at htau
    rw [htau, one_mul]

lemma x5bn_disc_pf {T A B : Type*} [Fintype T]
    {tau : Matrix T T ℂ} {sigma : Matrix (A × B) (A × B) ℂ} (htau : tau.trace = 1) :
    discardFirstAlice (productFactor tau sigma) = sigma := by
  ext i j
  simp only [discardFirstAlice, productFactor]
  rw [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag] at htau
  rw [htau, one_mul]

end

end QAlgorithms.Papers.Independent.Support50.P39

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P39

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq T] [DecidableEq A] [DecidableEq B]
    [Nonempty T] [Nonempty A] [Nonempty B]
    (tau : Matrix T T ℂ) (sigma : Matrix (A × B) (A × B) ℂ)
    (htau : IsDensityMatrix tau) (hsigma : IsDensityMatrix sigma)
    (ht : 0 < vnEntropy tau) (hb : 0 < clippedCoherentInformation sigma) :
    discardFirstAlice (productFactor tau sigma) = sigma ∧
    clippedCoherentInformation (productFactor tau sigma) =
      max (clippedCoherentInformation sigma - vnEntropy tau) 0 ∧
    clippedCoherentInformation (productFactor tau sigma) <
      clippedCoherentInformation (discardFirstAlice (productFactor tau sigma)) := by
  have hd := x5bn_disc_pf (B := B) (sigma := sigma) htau.2
  have hc : clippedCoherentInformation (productFactor tau sigma) =
      max (clippedCoherentInformation sigma - vnEntropy tau) 0 := by
    have hpos : 0 < vnEntropy (traceLeft sigma) - vnEntropy sigma := by
      unfold clippedCoherentInformation at hb
      by_contra h
      push Not at h
      rw [max_eq_right h] at hb
      exact lt_irrefl _ hb
    unfold clippedCoherentInformation
    rw [x5bn_tl_pf htau.2, x5bn_vn_pf htau hsigma, max_eq_left hpos.le]
    congr 1
    ring
  refine ⟨hd, hc, ?_⟩
  rw [hd, hc]
  rcases le_total (clippedCoherentInformation sigma - vnEntropy tau) 0 with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; linarith

