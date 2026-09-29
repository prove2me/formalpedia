-- Prove2me | solution 1 for centered_operator_symmetrization_q1_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:54:59.344137+00:00
-- url     : https://prove2.me/submissions/87dc3a76-d466-4bd7-b783-c2b68ccf1ef8

import Theorems.Thm_bernoulli_rademacher_symmetrization_contraction_moment_bound
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

set_option autoImplicit false

/-- CARVE 1: Bernoulli→Rademacher symmetrization at the operator-norm level,
a direct instantiation of the W3 brick
`bernoulli_rademacher_symmetrization_contraction_moment_bound` at `q = 1`,
`E := Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ` with the scoped
`Matrix.Norms.L2Operator` norm, and `v ab := y_ab ⊗ y_ab`. -/
theorem solution
    (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (S : SVD M r)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂) :
    bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
        (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ ab : Fin n₁ × Fin n₂,
              (((if ab ∈ Omega then (1:ℝ) else 0) - (m:ℝ)/((n₁:ℝ)*(n₂:ℝ))) •
                Matrix.vecMulVec
                  (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                  (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)
      ≤ 2 * bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
          (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ *
            (∑ Es : Finset (Fin n₁ × Fin n₂),
              ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) •
                      Matrix.vecMulVec
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)) := by
  -- abbreviations
  set p : ℝ := (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) with hp
  -- the matrix-valued summand `v ab` lives in the L2-operator `NormedSpace`
  set v : (Fin n₁ × Fin n₂) → Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
    fun ab => Matrix.vecMulVec
      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
    with hv
  -- p-bounds
  have hpos : (0:ℝ) < (n₁:ℝ) * (n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by
    rw [hp]; exact div_nonneg (by positivity) (le_of_lt hpos)
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hpos]
    have : (m:ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    rwa [Nat.cast_mul] at this
  have hinv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  -- W3 brick instantiated at q = 1, E = matrix space, v as above
  have hW3 := bernoulli_rademacher_symmetrization_contraction_moment_bound
    (κ := Fin n₁ × Fin n₂)
    (E := Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ)
    1 p hp0 hp1 v
  simp only [pow_one] at hW3
  -- the carve1 CLM-norm IS the L2-operator E-norm, definitionally
  -- (`‖toCLM (toEuclideanLin A)‖ = ‖A‖` by `rfl`); so we keep the same atom and
  -- only rearrange the constant factors.
  simp only [bernoulliExpectation, bernoulliObservationWeight]
  -- LHS = p⁻¹ * (∑ Ω, weight Ω * ‖centered Ω‖)
  rw [show
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
        p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
          (p⁻¹ *
            ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
              (∑ ab : Fin n₁ × Fin n₂,
                (((if ab ∈ Omega then (1:ℝ) else 0) - p) • v ab))))‖))
        = p⁻¹ *
          (∑ Omega : Finset (Fin n₁ × Fin n₂),
            p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1:ℝ) else 0) - p) • v ab))))‖)
      from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Omega _ => ?_)
        ring]
  -- RHS inner: p⁻¹ * (∑ Ω, ∑ Es, weight Ω * (1/2)^card * ‖signsum‖)
  rw [show
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
        p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
          (p⁻¹ *
            (∑ Es : Finset (Fin n₁ × Fin n₂),
              ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) • v ab))))‖)))
        = p⁻¹ *
          (∑ Omega : Finset (Fin n₁ × Fin n₂),
            ∑ Es : Finset (Fin n₁ × Fin n₂),
              p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
                ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) • v ab))))‖)
      from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Omega _ => ?_)
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Es _ => ?_)
        ring]
  -- pull the `2` into a `p⁻¹ * (2^1 * ...)` shape matching the scaled W3 RHS
  rw [show
      (2 : ℝ) * (p⁻¹ *
          (∑ Omega : Finset (Fin n₁ × Fin n₂),
            ∑ Es : Finset (Fin n₁ × Fin n₂),
              p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
                ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) • v ab))))‖))
        = p⁻¹ *
          (2 * ∑ Omega : Finset (Fin n₁ × Fin n₂),
            ∑ Es : Finset (Fin n₁ × Fin n₂),
              p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Omega.card) *
                ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) • v ab))))‖)
      from by ring]
  -- both sides are `p⁻¹ * (W3 side)`; the CLM-norms are defeq to the E-norms in hW3.
  exact mul_le_mul_of_nonneg_left hW3 hinv
