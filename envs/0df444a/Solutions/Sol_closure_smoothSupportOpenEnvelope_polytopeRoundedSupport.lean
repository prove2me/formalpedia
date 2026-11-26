-- Prove2me | solution 1 for closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:41.775979+00:00
-- url     : https://prove2.me/submissions/82573252-7d95-472d-9d11-a925cebb1cf3

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
import Theorems.Thm_convex_smoothSupportClosedEnvelope
import Theorems.Thm_isClosed_smoothSupportClosedEnvelope


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) =
      smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho) := by
  have hnonempty :
      (interior (smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho))).Nonempty := by
    exact nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hu hdelta hrho
  unfold smoothSupportOpenEnvelope
  calc
    closure (interior (smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho))) =
        closure (smoothSupportClosedEnvelope
          (polytopeRoundedSupport u delta rho)) :=
      Convex.closure_interior_eq_closure_of_nonempty_interior
        (convex_smoothSupportClosedEnvelope _) hnonempty
    _ = smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho) :=
      (isClosed_smoothSupportClosedEnvelope _).closure_eq
