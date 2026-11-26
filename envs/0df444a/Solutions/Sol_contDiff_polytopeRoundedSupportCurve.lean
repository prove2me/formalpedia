-- Prove2me | solution 1 for contDiff_polytopeRoundedSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:37.763205+00:00
-- url     : https://prove2.me/submissions/4544c770-1e5f-4397-9e45-e653c4484eb6

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_contDiff_smoothSupportCurve
import Theorems.Thm_contDiff_polytopeRoundedSupport


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) := by
  exact contDiff_smoothSupportCurve
    (contDiff_polytopeRoundedSupport hu delta rho)
