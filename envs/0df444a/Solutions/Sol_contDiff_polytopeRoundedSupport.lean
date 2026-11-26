-- Prove2me | solution 1 for contDiff_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:01.801836+00:00
-- url     : https://prove2.me/submissions/4d45fc12-235c-4cb6-b741-a4fb351903a7

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_contDiff_polytopeSoftSupport


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupport u delta rho) := by
  unfold polytopeRoundedSupport
  exact (contDiff_polytopeSoftSupport hu delta).add contDiff_const
