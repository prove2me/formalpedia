-- Prove2me | solution 1 for SoficGroups.cube_sum_le_dominant_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/40104058-8673-464f-81ad-a668c30ab28e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_cubeSum_le_dominant_mul_sum

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (ps : List ℝ) (m : ℝ)
    (hsum : ps.sum = 1)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (ps.map fun p => p ^ 3).sum ≤ m := by
  have hone : ∀ p ∈ ps, p ≤ (1 : ℝ) := by
    intro p hp
    have hsub : List.Sublist [p] ps := List.singleton_sublist.mpr hp
    have hle : ([p] : List ℝ).sum ≤ ps.sum :=
      hsub.sum_le_sum hpos
    simpa [hsum] using hle
  have h := cubeSum_le_dominant_mul_sum ps m hpos hone hdom
  simpa [hsum] using h
end SoficGroups
