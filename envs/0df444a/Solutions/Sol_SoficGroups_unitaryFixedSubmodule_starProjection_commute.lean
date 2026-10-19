-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_starProjection_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/8e52e46f-6fd8-41cd-8995-211774368bd9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_map_of_centralizes

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (g : G)
    (hg : ∀ k : K, Commute g (k : G)) (x : H) :
    (unitaryFixedSubmodule π K).starProjection (π g x) =
      π g ((unitaryFixedSubmodule π K).starProjection x) := by
  letI : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  have hmap := unitaryFixedSubmodule_map_of_centralizes π K g hg
  simpa [hmap] using
    Submodule.starProjection_map_apply (π g)
      (unitaryFixedSubmodule π K) (π g x)
end SoficGroups
