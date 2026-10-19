-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.modelMultiplicationBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/76c8f029-06e1-4c73-b07f-662fb88dfa35

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (g h : G) :
    Tendsto
      (fun n =>
        ((modelMultiplicationBad (A.model n) g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  simpa [modelMultiplicationBad, SoficGroups.normalizedHamming,
    hammingDist] using A.multiplicative g h
end SoficGroups.KunActualSoficRootRadius
