-- Prove2me | solution 1 for SoficGroups.midrankVariance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/a2ba9dad-f969-43c6-9e0a-679beadfeaa6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_midrankFirstMoment_eq
import Theorems.Thm_SoficGroups_midrankSecondMoment_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (ps : List ℝ) (hsum : ps.sum = 1) :
    midrankVariance ps = (1 - (ps.map fun p => p ^ 3).sum) / 12 := by
  unfold midrankVariance
  rw [midrankSecondMoment_eq, midrankFirstMoment_eq, hsum]
  ring
end SoficGroups
