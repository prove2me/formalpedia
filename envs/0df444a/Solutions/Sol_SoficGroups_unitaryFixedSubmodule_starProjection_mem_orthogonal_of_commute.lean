-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/2f06d5ec-1da3-4f6a-b356-55a25df42b53

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_of_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    (unitaryFixedSubmodule π K).starProjection x ∈
      (unitaryFixedSubmodule π Z)ᗮ := by
  letI : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hpz := unitaryFixedSubmodule_starProjection_mem_of_commute
    π K Z hcomm hz
  calc
    inner ℂ z ((unitaryFixedSubmodule π K).starProjection x) =
        inner ℂ ((unitaryFixedSubmodule π K).starProjection z) x :=
      (Submodule.inner_starProjection_left_eq_right
        (unitaryFixedSubmodule π K) z x).symm
    _ = 0 :=
      (Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) x).mp hx
        ((unitaryFixedSubmodule π K).starProjection z) hpz
end SoficGroups
