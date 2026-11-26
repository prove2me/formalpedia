-- Prove2me | solution 1 for closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:52.556082+00:00
-- url     : https://prove2.me/submissions/e9a1b35b-ed93-4795-83a8-abe5d26b9cf9

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
import Theorems.Thm_closure_smoothSupportOpenEnvelope_polytopeRoundedSupport

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by
  rw [closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
    hu hdelta hrho]
  exact
    smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho.le
