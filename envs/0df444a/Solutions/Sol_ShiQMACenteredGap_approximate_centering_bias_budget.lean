-- Prove2me | solution 1 for ShiQMACenteredGap.approximate_centering_bias_budget
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T09:21:00.033814+00:00
-- url     : https://prove2.me/submissions/e039cc0a-bff6-4f3a-85fa-6e35ea0f9c75

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_approximate_centering
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution {a b u : ℝ} (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hab : b ≤ a) (q : Nat)
    (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    let d := (a - b) / 8
    0 ≤ d ∧ d ≤ 1 / 2 ∧ (1 / 6 : ℝ) ≤ (2 * q : Nat) * d ∧
    (∀ t : ℝ, a ≤ t → 1 / 2 + d ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - d) := by
  dsimp only
  refine ⟨by linarith, by linarith, ?_, (approximate_centering hu).1,
    (approximate_centering hu).2⟩
  push_cast
  nlinarith
