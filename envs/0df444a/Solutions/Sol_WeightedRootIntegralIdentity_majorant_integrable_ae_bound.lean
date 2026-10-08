-- Prove2me | solution 1 for WeightedRootIntegralIdentity.majorant_integrable_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:32:40.050223+00:00
-- url     : https://prove2.me/submissions/ce24ffa8-2047-418f-86e1-bea4b9dda9b3

import Mathlib
open MeasureTheory

theorem solution {f g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.uIcc a b))
    (hbound : ∀ x ∈ Set.uIcc a b, ‖f x‖ ≤ g x) :
    IntegrableOn g (Set.uIcc a b) ∧
      ∀ᵐ x ∂Measure.restrict volume (Set.uIcc a b),
        ‖f x‖ ≤ g x := by
  constructor
  · exact hg.integrableOn_compact isCompact_uIcc
  · filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
    exact hbound x hx
