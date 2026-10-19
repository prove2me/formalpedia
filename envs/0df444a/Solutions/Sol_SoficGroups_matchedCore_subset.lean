-- Prove2me | solution 1 for SoficGroups.matchedCore_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/3c921c41-7ee9-4431-9b93-1dada1d47b3b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedCore_subset_retainedSupport

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    matchedCore R D ⊆ U :=
  (matchedCore_subset_retainedSupport R D).trans
    (matchedRetainedSupport_subset P R hR)
end SoficGroups
