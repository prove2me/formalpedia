-- Prove2me | solution 1 for SoficGroups.sum_card_component_inter_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/684a7e9a-fed3-4f89-a731-b6aee72c405d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_card_inter_partition

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) (hCU : C ⊆ U) :
    ∑ D ∈ Q.parts, (C ∩ D).card = C.card := by
  have h := sum_card_inter_partition Q C
  simpa [Finset.inter_comm, Finset.inter_eq_right.mpr hCU] using h
end SoficGroups
