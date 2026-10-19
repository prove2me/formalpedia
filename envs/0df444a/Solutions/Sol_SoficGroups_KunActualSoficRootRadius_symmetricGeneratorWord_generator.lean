-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/2021a03e-8a0e-49d0-8601-c91775c360ea

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
    (i : ↥S) (hi : (i : G) ≠ 1) :
    symmetricGeneratorWord S hsymmetric hgenerates (i : G) = [i] := by
  classical
  simp [symmetricGeneratorWord, hi, i.property]
end SoficGroups.KunActualSoficRootRadius
