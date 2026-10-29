-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T02:56:57.591288+00:00
-- url     : https://prove2.me/submissions/fd8c858c-0a28-4024-9176-a031122d4933

import Theorems.Thm_QuantumWalkSearch_SingularGap_equality_case
import Theorems.Thm_QuantumWalkSearch_SingularGap_path_chaining
import Theorems.Thm_QuantumWalkSearch_SingularGap_sqrt_stationary_eigenvector

open Matrix
open scoped ComplexConjugate
namespace QuantumWalkSearch.SingularGap
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem unit_eqcase_global (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) (hself : ∀ x, 0 < P x x)
    (u w : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : inner ℂ u (discriminantOp P π w) = 1) :
    ∀ x y : X, w y = w x * ((Real.sqrt (π y / π x) : ℝ) : ℂ) := by
  have heq := equality_case P π hP hirr hπ u w hu hw h1
  have hu_eq_w : u = w := by
    ext x
    have h := heq x x (hself x)
    simpa [ne_of_gt (hπ.pos x)] using h
  have hedge : ∀ x y : X, 0 < P x y →
      w y = w x * ((Real.sqrt (π y / π x) : ℝ) : ℂ) := by
    intro x y hxy
    have h := heq x y hxy
    rw [hu_eq_w] at h
    rw [Real.sqrt_div (hπ.pos x).le] at h
    rw [Real.sqrt_div (hπ.pos y).le]
    have hx : (Real.sqrt (π x) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hπ.pos x)))
    have hy : (Real.sqrt (π y) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hπ.pos y)))
    push_cast at h ⊢
    field_simp at h ⊢
    linear_combination -h
  exact path_chaining P π hP hirr hπ w hedge

theorem unit_global_not_orthogonal (π : X → ℝ)
    (u v : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hglobal_u : ∀ x y : X, u y = u x * ((Real.sqrt (π y / π x) : ℝ) : ℂ))
    (hglobal_v : ∀ x y : X, v y = v x * ((Real.sqrt (π y / π x) : ℝ) : ℂ)) :
    inner ℂ u v ≠ 0 := by
  classical
  haveI : Nonempty X := by
    by_contra h
    haveI : IsEmpty X := not_nonempty_iff.mp h
    have hz : u = 0 := by ext x; exact isEmptyElim x
    simp [hz] at hu
  let x₀ : X := Classical.choice inferInstance
  have hv₀ : v x₀ ≠ 0 := by
    intro hz
    have hvzero : v = 0 := by
      ext y
      rw [hglobal_v x₀ y, hz]
      simp
    simp [hvzero] at hv
  have hcol : (u x₀) • v = (v x₀) • u := by
    ext y
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [hglobal_v x₀ y, hglobal_u x₀ y]
    ring
  intro horth
  have h := congrArg (fun z : EuclideanSpace ℂ X => inner ℂ u z) hcol
  apply hv₀
  simpa [inner_smul_right, horth, inner_self_eq_norm_sq_to_K, hu] using h.symm

theorem singular_basis_global (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) (hself : ∀ x, 0 < P x x)
    (i : Fin (Fintype.card X)) (hi : discriminantSingularValues P π i = 1) :
    let T := discriminantOp P π
    let S := T.isSymmetric_adjoint_comp_self
    let w := S.eigenvectorBasis finrank_euclideanSpace i
    ∀ x y : X, w y = w x * ((Real.sqrt (π y / π x) : ℝ) : ℂ) := by
  let T := discriminantOp P π
  let S := T.isSymmetric_adjoint_comp_self
  let w := S.eigenvectorBasis finrank_euclideanSpace i
  change ∀ x y : X, w y = w x * ((Real.sqrt (π y / π x) : ℝ) : ℂ)
  have hw : ‖w‖ = 1 := (S.eigenvectorBasis finrank_euclideanSpace).orthonormal.norm_eq_one i
  have heq : ‖T w‖ ^ 2 = S.eigenvalues finrank_euclideanSpace i := by
    have h := T.adjoint_inner_right w (T w)
    have heigen := S.apply_eigenvectorBasis finrank_euclideanSpace i
    change T.adjoint (T w) = (S.eigenvalues finrank_euclideanSpace i : ℂ) • w at heigen
    rw [heigen] at h
    have h' := congrArg Complex.re h.symm
    have hre : ((‖T w‖ : ℂ) ^ 2).re = ‖T w‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simpa [inner_smul_right, inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, hw, hre] using h'
  have hsq := T.sq_singularValues_fin finrank_euclideanSpace i
  change T.singularValues i = 1 at hi
  rw [hi] at hsq
  have hnormsq : ‖T w‖ ^ 2 = 1 := by rw [heq, ← hsq]; norm_num
  have hnorm : ‖T w‖ = 1 := by nlinarith [norm_nonneg (T w)]
  have hinner : inner ℂ (T w) (T w) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  exact unit_eqcase_global P π hP hirr hπ hself (T w) w hnorm hw hinner

theorem stationary_is_singular_vector (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) :
    let T := discriminantOp P π
    (T.adjoint ∘ₗ T) (sqrtStationary π) = sqrtStationary π ∧
      sqrtStationary π ≠ 0 := by
  let v := sqrtStationary π
  let T := discriminantOp P π
  change (T.adjoint ∘ₗ T) v = v ∧ v ≠ 0
  have hvnorm : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v, sqrtStationary, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hπ.pos _).le]
    exact hπ.sum_eq_one
  have hvne : v ≠ 0 := by
    intro h
    simp [h] at hvnorm
  have hT : T v = v := by
    apply WithLp.ofLp_injective
    simpa [T, v, discriminantOp, Matrix.toEuclideanLin_apply] using
      (sqrt_stationary_eigenvector P π hP hirr hπ).1
  have hTadj : T.adjoint v = v := by
    apply WithLp.ofLp_injective
    change ((Matrix.toEuclideanLin (discriminant P π)).adjoint v).ofLp = v.ofLp
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin_apply]
    change (discriminant P π)ᴴ *ᵥ v.ofLp = v.ofLp
    ext y
    have h := congrFun (sqrt_stationary_eigenvector P π hP hirr hπ).2 y
    simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      discriminant, v, sqrtStationary, mul_comm] using h
  exact ⟨by simpa only [LinearMap.comp_apply, hT] using hTadj, hvne⟩

theorem singular_index_unique (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) (hself : ∀ x, 0 < P x x)
    (i j : Fin (Fintype.card X))
    (hi : discriminantSingularValues P π i = 1)
    (hj : discriminantSingularValues P π j = 1) : i = j := by
  classical
  by_contra hij
  let T := discriminantOp P π
  let S := T.isSymmetric_adjoint_comp_self
  let b := S.eigenvectorBasis finrank_euclideanSpace
  have horth : inner ℂ (b i) (b j) = 0 := b.orthonormal.inner_eq_zero hij
  have hiG := singular_basis_global P π hP hirr hπ hself i hi
  have hjG := singular_basis_global P π hP hirr hπ hself j hj
  have hn : inner ℂ (b i) (b j) ≠ 0 :=
    unit_global_not_orthogonal π (b i) (b j) (b.orthonormal.norm_eq_one i)
      (b.orthonormal.norm_eq_one j) hiG hjG
  exact hn horth

end QuantumWalkSearch.SingularGap

open QuantumWalkSearch.SingularGap

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) (hself : ∀ x, 0 < P x x) :
    ((Finset.range (Fintype.card X)).filter
        (fun i => discriminantSingularValues P π i = 1)).card = 1 := by
  classical
  let T := discriminantOp P π
  let S := T.isSymmetric_adjoint_comp_self
  have hv := stationary_is_singular_vector P π hP hirr hπ
  have hvec : Module.End.HasEigenvector (T.adjoint ∘ₗ T) (1 : ℂ) (sqrtStationary π) := by
    refine ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv.1
  have heval := S.exists_eigenvalues_eq finrank_euclideanSpace
    (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  obtain ⟨i, hi⟩ := heval
  have hi' : S.eigenvalues finrank_euclideanSpace i = 1 := by
    have hh := congrArg Complex.re hi
    simpa using hh
  have hsq := T.sq_singularValues_fin finrank_euclideanSpace i
  rw [hi'] at hsq
  have hsi : discriminantSingularValues P π i = 1 := by
    change T.singularValues i = 1
    nlinarith [T.singularValues_nonneg i]
  rw [Finset.card_eq_one_iff_existsUnique]
  refine ⟨i, ?_, ?_⟩
  · simp [i.isLt, hsi]
  · intro j hj
    have hj' : j < Fintype.card X ∧ discriminantSingularValues P π j = 1 := by simpa using hj
    have hij := singular_index_unique P π hP hirr hπ hself ⟨j, hj'.1⟩ i hj'.2 hsi
    exact congrArg Fin.val hij

