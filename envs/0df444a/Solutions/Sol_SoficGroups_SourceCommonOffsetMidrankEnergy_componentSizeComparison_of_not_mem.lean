-- Prove2me | solution 1 for SoficGroups.SourceCommonOffsetMidrankEnergy.componentSizeComparison_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/5df33865-f2da-4bb0-b888-65d80944817b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonOffsetMidrankEnergy
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ)
    (i : ι) (x : V)
    (hx : (i, x) ∉ componentSizeComparisonBad Q p eta) :
    (1 - eta) * realComponentSize Q x ≤
      realComponentSize Q (p i x) := by
  classical
  by_contra h
  apply hx
  unfold componentSizeComparisonBad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
end SoficGroups.SourceCommonOffsetMidrankEnergy
