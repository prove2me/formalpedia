-- Prove2me | solution 1 for WhitneyEmbedding.finite_injective_immersion_from_separating_family_main
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:14:42.629282+00:00
-- url     : https://prove2.me/submissions/1f3ac896-d678-4a2e-b743-b432e42da5f8

import Mathlib
import Theorems.Thm_WhitneyEmbedding_finite_injective_immersion_from_separating_family
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (seq : ℕ → M → ℝ)
    (hseq_diff : ∀ k, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (seq k))
    (hseq_comp : ∀ k, HasCompactSupport (seq k))
    (hseq_sep : ∀ x y, x ≠ y → ∃ k, seq k x ≠ seq k y)
    (hseq_tan : ∀ x, ∀ (v : TangentSpace (𝓡 n) x), v ≠ 0 → ∃ k, mfderiv (𝓡 n) 𝓘(ℝ) (seq k) x v ≠ 0) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by
  first
  | exact WhitneyEmbedding.finite_injective_immersion_from_separating_family
  | (apply WhitneyEmbedding.finite_injective_immersion_from_separating_family <;> assumption)
  | (intros; apply WhitneyEmbedding.finite_injective_immersion_from_separating_family <;> assumption)
