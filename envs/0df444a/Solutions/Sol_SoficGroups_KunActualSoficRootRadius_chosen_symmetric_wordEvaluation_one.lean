-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosen_symmetric_wordEvaluation_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/d83c3950-8850-4448-bc21-5f5be55efdd8

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
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) :
    chosenWordEvaluation A (fun i : ↥S => (i : G))
      (symmetricGeneratorWord S hsymmetric hgenerates) n 1 = 1 := by
  simp [chosenWordEvaluation]
end SoficGroups.KunActualSoficRootRadius
