-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T02:10:01.588793+00:00
-- url     : https://prove2.me/submissions/f0c56f11-b893-48d0-90f3-438f6b795d61

import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

open QuantumWalkSearch.SingularGap

private theorem weighted_norm_sum_sq_le {X : Type*} [Fintype X]
    (p : X → ℝ) (z : X → ℂ) (hp : ∀ x, 0 ≤ p x) :
    ‖∑ x, (p x : ℂ) * z x‖ ^ 2 ≤ (∑ x, p x) * ∑ x, p x * ‖z x‖ ^ 2 := by
  have hnorm : ‖∑ x, (p x : ℂ) * z x‖ ≤ ∑ x, p x * ‖z x‖ := by
    calc
      _ ≤ ∑ x, ‖(p x : ℂ) * z x‖ := norm_sum_le _ _
      _ = _ := by simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg, hp]
  have hsq : (∑ x, p x * ‖z x‖) ^ 2 ≤ (∑ x, p x) * ∑ x, p x * ‖z x‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · exact fun x _ => hp x
    · exact fun x _ => mul_nonneg (hp x) (sq_nonneg _)
    · intro x _
      ring_nf
      exact le_rfl
  exact le_trans (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun x _ =>
    mul_nonneg (hp x) (norm_nonneg _)) |>.2 hnorm) hsq

private theorem singular_values_le_one_of_contract
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (i : ℕ) : T.singularValues i ≤ 1 := by
  by_cases hi : Module.finrank ℂ E ≤ i
  · rw [T.singularValues_of_finrank_le hi]
    norm_num
  · have hi' : i < Module.finrank ℂ E := Nat.lt_of_not_ge hi
    let j : Fin (Module.finrank ℂ E) := ⟨i, hi'⟩
    let S := T.isSymmetric_adjoint_comp_self
    let v := S.eigenvectorBasis rfl j
    have hv : ‖v‖ = 1 := (S.eigenvectorBasis rfl).orthonormal.norm_eq_one j
    have heq : ‖T v‖ ^ 2 = S.eigenvalues rfl j := by
      have h := T.adjoint_inner_right v (T v)
      have heigen := S.apply_eigenvectorBasis rfl j
      change (T.adjoint ∘ₗ T) v = (S.eigenvalues rfl j : ℂ) • v at heigen
      change T.adjoint (T v) = (S.eigenvalues rfl j : ℂ) • v at heigen
      rw [heigen] at h
      have h' := congrArg Complex.re h.symm
      have hre : ((‖T v‖ : ℂ) ^ 2).re = ‖T v‖ ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      simpa [inner_smul_right, inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, hv, hre] using h'
    have hsq : ‖T v‖ ^ 2 ≤ 1 := by
      have := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hT v)
      simpa [hv] using this
    have hsing := T.sq_singularValues_of_lt rfl hi'
    have hnonneg := T.singularValues_nonneg i
    change T.singularValues i ^ 2 = S.eigenvalues rfl j at hsing
    rw [← heq] at hsing
    nlinarith

private theorem discriminant_contract {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDistribution P π)
    (v : EuclideanSpace ℂ X) : ‖discriminantOp P π v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ x, ‖discriminantOp P π v x‖ ^ 2 ≤
        ∑ x, π x * ∑ y, P x y * ‖v y / (Real.sqrt (π y) : ℂ)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hrow : discriminantOp P π v x = (Real.sqrt (π x) : ℂ) *
          ∑ y, (P x y : ℂ) * (v y / (Real.sqrt (π y) : ℂ)) := by
        simp only [discriminantOp, Matrix.toEuclideanLin_apply, Matrix.mulVec,
          dotProduct, discriminant, Matrix.of_apply, PiLp.toLp_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        push_cast
        ring
      rw [hrow, norm_mul, mul_pow]
      have hsqrt : ‖(Real.sqrt (π x) : ℂ)‖ ^ 2 = π x := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          Real.sq_sqrt (hπ.pos x).le
      rw [hsqrt]
      have hw := weighted_norm_sum_sq_le (P x)
        (fun y => v y / (Real.sqrt (π y) : ℂ)) (hP.1 x)
      rw [Matrix.sum_row_of_mem_rowStochastic hP x, one_mul] at hw
      exact mul_le_mul_of_nonneg_left hw (hπ.pos x).le
    _ = ∑ y, (∑ x, π x * P x y) * ‖v y / (Real.sqrt (π y) : ℂ)‖ ^ 2 := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ y, ‖v y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hπ.stationary y, norm_div, div_pow]
      have hsqrt : ‖(Real.sqrt (π y) : ℂ)‖ ^ 2 = π y := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          Real.sq_sqrt (hπ.pos y).le
      rw [hsqrt]
      field_simp [ne_of_gt (hπ.pos y)]

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) :
    ∀ i : ℕ, 0 ≤ discriminantSingularValues P π i ∧ discriminantSingularValues P π i ≤ 1 := by
  intro i
  exact ⟨(discriminantOp P π).singularValues_nonneg i,
    singular_values_le_one_of_contract _ (discriminant_contract P π hP hπ) i⟩

