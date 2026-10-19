-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosen_symmetric_wordEvaluation_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/15bf8cd4-3b5c-4a0f-b5cd-5aa5f6d21b49

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_generator

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
    (n : ℕ) (i : ↥S) :
    chosenWordEvaluation A (fun j : ↥S => (j : G))
      (symmetricGeneratorWord S hsymmetric hgenerates)
      n (i : G) =
        (A.model n).action (i : G) := by
  classical
  by_cases hi : (i : G) = 1
  · simp [chosenWordEvaluation, hi,
      SoficGroups.PermutationModel.map_one]
  · rw [chosenWordEvaluation,
      symmetricGeneratorWord_generator S hsymmetric hgenerates i hi]
    simp
end SoficGroups.KunActualSoficRootRadius
