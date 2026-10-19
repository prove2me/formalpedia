-- Prove2me | solution 1 for SoficGroups.KunExactKazhdanGeneratorChange.exists_kazhdanPair_with_exact_symmetric_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/628d844b-12c1-4c8b-a479-8ffbca8a26f2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunExactKazhdanGeneratorChange_kazhdanPairOnSymmetricGeneratingFinset_generators

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactKazhdanGeneratorChange
universe u v
namespace SoficGroups.KunExactKazhdanGeneratorChange
theorem _root_.solution
    {G : Type u} [Group G]
    [SoficGroups.HasPropertyT.{u, v} G]
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    ∃ P : SoficGroups.KazhdanPair.{u, v} G,
      P.generators = S := by
  obtain ⟨P⟩ :=
    SoficGroups.HasPropertyT.exists_kazhdanPair (G := G)
  exact ⟨kazhdanPairOnSymmetricGeneratingFinset
    P S hsymmetric hgenerates,
    kazhdanPairOnSymmetricGeneratingFinset_generators
      P S hsymmetric hgenerates⟩
end SoficGroups.KunExactKazhdanGeneratorChange
