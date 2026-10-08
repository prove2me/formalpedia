-- Prove2me | solution 1 for WeightedRootIntegralIdentity.ae_ne_const_restrict_uIcc
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:18:18.56183+00:00
-- url     : https://prove2.me/submissions/bffad2a0-bbde-4ab3-9f36-9d90bd38fab1

import Mathlib
open MeasureTheory

theorem solution (l c : ℝ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Set.uIcc l c : Set ℝ)), x ≠ c := by
  exact Measure.ae_ne (volume.restrict (Set.uIcc l c : Set ℝ)) c
