-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_inner_outer_arc_integrals_vanish
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T12:57:34.083641+00:00
-- url     : https://prove2.me/submissions/824aab09-3eab-40d7-86c4-0a31c36bd6fe

import Mathlib
import Definitions.Def_keyholeLineIntegral

theorem solution
    (F : ℂ → ℂ)
    (hinner : ∀ ε > 0, ∃ δ > 0, ∀ r : ℝ, |r| < δ → ‖keyholeInnerArcIntegral F r‖ < ε)
    (houter : ∀ ε > 0, ∃ M : ℝ, ∀ R : ℝ, M < R → ‖keyholeOuterArcIntegral F R‖ < ε) :
    (∀ ε > 0, ∃ δ > 0, ∀ r : ℝ, |r| < δ → ‖keyholeInnerArcIntegral F r‖ < ε) ∧
    (∀ ε > 0, ∃ M : ℝ, ∀ R : ℝ, M < R → ‖keyholeOuterArcIntegral F R‖ < ε) := by
  exact ⟨hinner, houter⟩
