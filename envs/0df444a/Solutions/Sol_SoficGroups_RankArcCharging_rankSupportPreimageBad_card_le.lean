-- Prove2me | solution 1 for SoficGroups.RankArcCharging.rankSupportPreimageBad_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/8ad27bf6-79ae-4407-a6c8-7a1058264bcf

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (U S : Finset V) (w : Equiv.Perm V) :
    (rankSupportPreimageBad U S w).card ≤ (U \ S).card := by
  apply Finset.card_le_card_of_injOn w
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact w.injective hxy
end SoficGroups.RankArcCharging
