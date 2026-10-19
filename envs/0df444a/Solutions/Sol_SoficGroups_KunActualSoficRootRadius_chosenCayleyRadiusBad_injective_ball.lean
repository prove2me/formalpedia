-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_injective_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/951122d4-3e09-47a3-946c-89636b69f501

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteRootBad_injective_word_evaluation

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (w : G → List ↥S) (n r : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenCayleyRadiusBad A S w n r) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑(S ^ r) : Set G) := by
  exact chosenFiniteRootBad_injective_word_evaluation
    A (fun i : ↥S => (i : G)) w (S ^ r) n hx
end SoficGroups.KunActualSoficRootRadius
