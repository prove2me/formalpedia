-- Prove2me | solution 1 for SoficGroups.partitionComponentSize_eq_card_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/80ffeb04-48a8-4fe2-a263-fc57da5ea256

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) (hC : C ∈ Q.parts)
    (x : V) (hx : x ∈ C) :
    partitionComponentSize Q x = C.card := by
  unfold partitionComponentSize
  rw [Q.part_eq_of_mem hC hx]
end SoficGroups
