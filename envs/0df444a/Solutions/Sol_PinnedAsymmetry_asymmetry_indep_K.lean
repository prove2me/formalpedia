-- Prove2me | solution 1 for PinnedAsymmetry.asymmetry_indep_K
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:32:23.329095+00:00
-- url     : https://prove2.me/submissions/71d87e6a-f62a-474f-9373-bf2aa5ed0905

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

namespace PinnedAsymmetrySol
open PinnedAsymmetry

theorem radicand_even (K c β q : ℝ) :
    (β * c * sin (-q)) ^ 2 + K + 2 * c * (1 - cos (-q))
      = (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q) := by
  rw [sin_neg, cos_neg]; ring

theorem asymmetry (K c β q : ℝ) :
    omega K c β q - omega K c β (-q) = 2 * β * c * sin q := by
  unfold omega
  rw [radicand_even, sin_neg]; ring

end PinnedAsymmetrySol

open PinnedAsymmetry PinnedAsymmetrySol

theorem solution (K₁ K₂ c β q : ℝ) :
    omega K₁ c β q - omega K₁ c β (-q) = omega K₂ c β q - omega K₂ c β (-q) := by
  rw [asymmetry, asymmetry]
