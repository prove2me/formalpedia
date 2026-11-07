-- Prove2me | solution 1 for StatUnlearn.shiftedGaussianShell_eq_ball
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T18:41:58.828447+00:00
-- url     : https://prove2.me/submissions/cc7b868b-ec46-474f-8fbc-71a7d6a5ca43

/-
Proof (reduction) for `StatUnlearn.shiftedGaussianShell_eq_ball`.

The only nontrivial input is the triangle inequality for the Mahalanobis distance
(`StatUnlearn.mahalanobis_triangle`, a milestone of the same mission). Everything else is
the arithmetic of the separation hypothesis and the evenness of the quadratic form, which is
proved here.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Theorems.Thm_StatUnlearn_mahalanobis_triangle

open MeasureTheory
open StatUnlearn

theorem solution {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (μ₁ ν₁ : EuclideanSpace ℝ (Fin d)) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (h : Real.sqrt (inner ℝ (μ₁ - ν₁) (Matrix.toEuclideanLin S⁻¹ (μ₁ - ν₁))) - ε ≥ α) :
    ({μ : EuclideanSpace ℝ (Fin d) |
        α ≤ Real.sqrt (inner ℝ (μ₁ - μ) (Matrix.toEuclideanLin S⁻¹ (μ₁ - μ))) ∧
        Real.sqrt (inner ℝ (ν₁ - μ) (Matrix.toEuclideanLin S⁻¹ (ν₁ - μ))) ≤ ε}
      : Set (EuclideanSpace ℝ (Fin d)))
      = ({μ : EuclideanSpace ℝ (Fin d) |
        Real.sqrt (inner ℝ (ν₁ - μ) (Matrix.toEuclideanLin S⁻¹ (ν₁ - μ))) ≤ ε}
      : Set (EuclideanSpace ℝ (Fin d))) := by
  -- the quadratic form is even, so `ρ (-z) = ρ z`
  have hneg : ∀ z : EuclideanSpace ℝ (Fin d),
      Real.sqrt (inner ℝ (-z) (Matrix.toEuclideanLin S⁻¹ (-z)))
        = Real.sqrt (inner ℝ z (Matrix.toEuclideanLin S⁻¹ z)) := by
    intro z
    congr 1
    simp
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h₂⟩
    exact h₂
  · intro h₂
    refine ⟨?_, h₂⟩
    -- `Δ ≤ ρ (μ₁ - μ) + ρ (ν₁ - μ)` from the triangle inequality applied to
    -- `x = μ₁ - μ`, `y = -(ν₁ - μ)`
    have htri := mahalanobis_triangle S hS (μ₁ - μ) (-(ν₁ - μ))
    have e : (μ₁ - μ) + -(ν₁ - μ) = μ₁ - ν₁ := by abel
    have htri' : Real.sqrt (inner ℝ (μ₁ - ν₁) (Matrix.toEuclideanLin S⁻¹ (μ₁ - ν₁)))
        ≤ Real.sqrt (inner ℝ (μ₁ - μ) (Matrix.toEuclideanLin S⁻¹ (μ₁ - μ)))
          + Real.sqrt (inner ℝ (ν₁ - μ) (Matrix.toEuclideanLin S⁻¹ (ν₁ - μ))) := by
      rw [← e, ← hneg (ν₁ - μ)]
      exact htri
    linarith
