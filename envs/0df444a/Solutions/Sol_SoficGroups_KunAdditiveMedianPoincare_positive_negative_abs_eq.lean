-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.positive_negative_abs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/72954a8d-0a7f-4daa-83a1-c8bc9d2f5560

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution (a b : ℝ) :
    |max a 0 - max b 0| +
      |max (-a) 0 - max (-b) 0| = |a - b| := by
  rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
    rcases le_total a b with hab | hab <;>
    simp_all [abs_of_nonneg, abs_of_nonpos] <;> linarith
end SoficGroups.KunAdditiveMedianPoincare
