-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/250eb379-eae7-4721-af02-862bd95ef9f0

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
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (g : G) :
    (((symmetricGeneratorWord S hsymmetric hgenerates g).map
      fun i : ↥S => (i : G)).prod) = g := by
  classical
  unfold symmetricGeneratorWord
  split <;> rename_i hone
  · simp [hone]
  · split <;> rename_i hg
    · simp
    · exact (exists_generator_word_of_symmetric_generates
        S hsymmetric hgenerates g).choose_spec
end SoficGroups.KunActualSoficRootRadius
