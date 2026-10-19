-- Prove2me | solution 1 for SoficGroups.matchedWordPreimageBad_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/8c2486ec-e1a6-476a-8770-7c5467b56ec4

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
    {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) :
    (matchedWordPreimageBad U R D w).card ≤
      (U \ matchedCore R D).card := by
  apply Finset.card_le_card_of_injOn w
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact w.injective hxy
end SoficGroups
