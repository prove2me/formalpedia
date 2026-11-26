-- Prove2me | solution 1 for contDiff_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:16.669422+00:00
-- url     : https://prove2.me/submissions/70cde578-7d57-4c89-a0c5-725bbba2a62e

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_contDiff_smoothSupportUnitNormal
import Theorems.Thm_contDiff_smoothSupportUnitTangent

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (smoothSupportCurve h) := by
  have hderiv : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  exact (hsmooth.smul contDiff_smoothSupportUnitNormal).add
    (hderiv.smul contDiff_smoothSupportUnitTangent)
