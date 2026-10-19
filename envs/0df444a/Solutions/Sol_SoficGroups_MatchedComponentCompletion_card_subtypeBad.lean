-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.card_subtypeBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/da89352d-314f-44a5-a5e7-78b89e5677a8

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) :
    (subtypeBad Z E).card = (Z ∩ E).card := by
  classical
  have hmap :
      (subtypeBad Z E).map
        (Function.Embedding.subtype (fun x : V => x ∈ Z)) = Z ∩ E := by
    ext x
    simp [subtypeBad, and_comm]
  simpa using congrArg Finset.card hmap
end SoficGroups.MatchedComponentCompletion
