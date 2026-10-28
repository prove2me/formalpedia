-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.maxResidual_almostGradient_signed_active
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:11:32.199064+00:00
-- url     : https://prove2.me/submissions/d2cf017b-5b63-40b0-8d92-422a50fe3df1

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
import Theorems.Thm_almostGradient_signed_active_inline
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, maxResidual ψ x ≠ 0 →
      ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧ g = σ • gradient (ψ i) x ∧
          σ * ψ i x = maxResidual ψ x ∧ |ψ i x| = maxResidual ψ x :=
  almostGradient_signed_active_inline ψ xstar U hU hψ
