-- Prove2me | solution 1 for SoficGroups.agreementSet_card_add_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/bed7b601-4f7f-46c1-b7aa-0f0c46d2a24f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V] (c c' : Equiv.Perm V) :
    (agreementSet c c').card +
      hammingDist (fun x => c x) (fun x => c' x) = Fintype.card V := by
  simpa [agreementSet, hammingDist] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (fun x => c x = c' x))
end SoficGroups
