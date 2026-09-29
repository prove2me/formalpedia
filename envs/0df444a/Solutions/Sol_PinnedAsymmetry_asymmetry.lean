-- Prove2me | solution 1 for PinnedAsymmetry.asymmetry
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:32:22.134285+00:00
-- url     : https://prove2.me/submissions/140b9eef-e010-409c-9aa8-1060b444d3a9

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

namespace PinnedAsymmetrySol
open PinnedAsymmetry

theorem radicand_even (K c β q : ℝ) :
    (β * c * sin (-q)) ^ 2 + K + 2 * c * (1 - cos (-q))
      = (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q) := by
  rw [sin_neg, cos_neg]; ring

end PinnedAsymmetrySol

open PinnedAsymmetry PinnedAsymmetrySol

theorem solution (K c β q : ℝ) :
    omega K c β q - omega K c β (-q) = 2 * β * c * sin q := by
  unfold omega
  rw [radicand_even, sin_neg]; ring
