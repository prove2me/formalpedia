-- Prove2me | solution 1 for PinnedAsymmetry.omega_is_root
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:32:20.135681+00:00
-- url     : https://prove2.me/submissions/bda23c9e-56a0-4ac8-be30-c8e4d0b1162f

import Mathlib
import Definitions.Def_PinnedAsymmetry_omega

open Real

open PinnedAsymmetry

theorem solution (K c β q : ℝ)
    (h : 0 ≤ (β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q)) :
    (omega K c β q) ^ 2 - 2 * β * c * sin q * omega K c β q
      - (K + 2 * c * (1 - cos q)) = 0 := by
  unfold omega
  have hs := Real.sq_sqrt h
  nlinarith [hs]
