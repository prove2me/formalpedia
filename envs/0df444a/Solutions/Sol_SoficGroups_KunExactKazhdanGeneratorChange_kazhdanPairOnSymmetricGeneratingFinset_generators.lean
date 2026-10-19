-- Prove2me | solution 1 for SoficGroups.KunExactKazhdanGeneratorChange.kazhdanPairOnSymmetricGeneratingFinset_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/c94c46e0-20b0-49c8-84fa-9fbaf6df9dfe

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactKazhdanGeneratorChange
universe u v
namespace SoficGroups.KunExactKazhdanGeneratorChange
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, v} G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    (kazhdanPairOnSymmetricGeneratingFinset
      P S hsymmetric hgenerates).generators = S := by
  rfl
end SoficGroups.KunExactKazhdanGeneratorChange
