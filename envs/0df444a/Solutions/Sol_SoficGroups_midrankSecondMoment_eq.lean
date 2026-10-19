-- Prove2me | solution 1 for SoficGroups.midrankSecondMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/b5dc1db4-674c-4253-95ac-20bdf94fb886

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (a : ℝ) (ps : List ℝ) :
    midrankSecondMoment a ps =
      ((a + ps.sum) ^ 3 - a ^ 3) / 3 -
        (ps.map fun p => p ^ 3).sum / 12 := by
  induction ps generalizing a with
  | nil => simp [midrankSecondMoment]
  | cons p ps ih =>
      simp only [midrankSecondMoment, List.sum_cons, List.map_cons]
      rw [ih (a + p)]
      ring
end SoficGroups
