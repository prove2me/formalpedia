-- Prove2me | solution 2 for ShorNonsmooth.NonlinEq.max_residual_almost_gradient_near_solution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:12:19.609687+00:00
-- url     : https://prove2.me/submissions/2ea58404-02af-44f9-8451-5e715a475662

import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_local_inverse_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_active_signed_inner_approx
import Theorems.Thm_almostGradient_signed_active_inline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (hroot : ∀ i, ψ i xstar = 0) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ nhds xstar) (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
      (1 - δ) * maxResidual ψ x ≤ inner ℝ g (x - xstar) ∧
        inner ℝ g (x - xstar) ≤ (1 + δ) * maxResidual ψ x := by
  classical
  obtain ⟨Vinv, hVinv, C, hCpos, hinv⟩ :=
    maxResidual_local_inverse_bound ψ xstar hroot U hU hψ hJ
  obtain ⟨Vapprox, hVapprox, happrox⟩ :=
    maxResidual_active_signed_inner_approx ψ xstar hroot U hU hψ hJ δ hδ
  obtain ⟨Vactive, hVactive, hactive⟩ :=
    almostGradient_signed_active_inline ψ xstar U hU hψ
  refine ⟨Vinv ∩ (Vapprox ∩ Vactive),
    Filter.inter_mem hVinv (Filter.inter_mem hVapprox hVactive), ?_⟩
  intro x hx g hg
  rcases hx with ⟨hxinv, hxapprox, hxactive⟩
  by_cases hF0 : maxResidual ψ x = 0
  · have hsub : x - xstar = 0 := by
      have hle := hinv x hxinv
      have hzero : ‖x - xstar‖ = 0 := by
        apply le_antisymm _ (norm_nonneg _)
        simpa [hF0] using hle
      exact norm_eq_zero.mp hzero
    simp [hsub, hF0]
  · rcases hactive x hxactive hF0 g hg with
      ⟨i, σ, hσ2, hgσ, hσF, hψactive⟩
    have hgrad := happrox x hxapprox i hψactive
    have hσabs : |σ| = 1 := by
      have hσsq : |σ| ^ 2 = 1 := by simpa [sq_abs] using hσ2
      nlinarith [abs_nonneg σ]
    let A := inner ℝ (gradient (ψ i) x) (x - xstar)
    have hscaled : |σ * A - maxResidual ψ x| ≤ δ * maxResidual ψ x := by
      calc
        |σ * A - maxResidual ψ x| = |σ * A - σ * ψ i x| := by rw [hσF]
        _ = |σ * (A - ψ i x)| := by ring_nf
        _ = |σ| * |A - ψ i x| := abs_mul _ _
        _ = |A - ψ i x| := by rw [hσabs, one_mul]
        _ ≤ δ * maxResidual ψ x := by simpa [A] using hgrad
    have hle := abs_le.mp hscaled
    have hinner : inner ℝ g (x - xstar) = σ * A := by
      simp [hgσ, A, inner_smul_left]
    rw [hinner]
    constructor <;> linarith [hle.1, hle.2]
