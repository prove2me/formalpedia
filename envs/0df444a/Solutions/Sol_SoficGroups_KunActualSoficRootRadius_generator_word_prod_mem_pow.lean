-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.generator_word_prod_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/67834e5c-fba1-461b-813c-f10d56ec8de0

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
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (l : List ↥S) :
    ((l.map fun i : ↥S => (i : G)).prod) ∈ S ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simpa [pow_succ', List.prod_cons] using
        (Finset.mul_mem_mul a.property ih)
end SoficGroups.KunActualSoficRootRadius
