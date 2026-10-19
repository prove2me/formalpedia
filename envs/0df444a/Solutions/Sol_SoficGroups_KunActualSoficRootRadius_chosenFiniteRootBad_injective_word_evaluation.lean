-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenFiniteRootBad_injective_word_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/d4275bd7-d850-45ba-9dbb-ed5c7552ba16

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_injective_word_evaluation

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteRootBad A s w F n) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑F : Set G) := by
  apply finiteRootBad_injective_word_evaluation
    (A.model n) F
  intro hbad
  exact hx (Finset.mem_union_left _ hbad)
end SoficGroups.KunActualSoficRootRadius
