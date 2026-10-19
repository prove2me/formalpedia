-- Prove2me | solution 1 for SoficGroups.midrankFirstMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/86cf83af-dc2f-4162-9191-6f10d0bb867c

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
    midrankFirstMoment a ps = ((a + ps.sum) ^ 2 - a ^ 2) / 2 := by
  induction ps generalizing a with
  | nil => simp [midrankFirstMoment]
  | cons p ps ih =>
      simp only [midrankFirstMoment, List.sum_cons]
      rw [ih (a + p)]
      ring
end SoficGroups
