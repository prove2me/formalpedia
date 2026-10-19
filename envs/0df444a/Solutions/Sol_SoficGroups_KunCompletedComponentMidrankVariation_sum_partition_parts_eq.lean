-- Prove2me | solution 1 for SoficGroups.KunCompletedComponentMidrankVariation.sum_partition_parts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/d11b7bd7-b880-4294-bb82-26c4919bafa7

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCompletedComponentMidrankVariation
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) (f : V → ℝ) :
    (∑ C ∈ P.parts, ∑ x ∈ C, f x) = ∑ x : V, f x := by
  classical
  calc
    (∑ C ∈ P.parts, ∑ x ∈ C, f x) =
        ∑ x ∈ P.parts.biUnion id, f x := by
          symm
          exact Finset.sum_biUnion P.disjoint
    _ = ∑ x : V, f x := by rw [P.biUnion_parts]
end SoficGroups.KunCompletedComponentMidrankVariation
