-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.finiteRootBad_injective_word_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/94b52d8c-d5d0-400c-8ac9-25725fae01d6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_separated

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    Set.InjOn (fun g : G => M.action g x) (↑F : Set G) := by
  intro g hg h hh heq
  by_contra hne
  exact finiteRootBad_separated M F hg hh hne hx heq
end SoficGroups.KunActualSoficRootRadius
