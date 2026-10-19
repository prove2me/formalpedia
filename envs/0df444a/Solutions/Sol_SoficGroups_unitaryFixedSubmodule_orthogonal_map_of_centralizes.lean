-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_orthogonal_map_of_centralizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/9346fb80-bb77-44f6-8d75-5433e75c2fe0

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
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (Z : Subgroup G) (g : G)
    (hg : ∀ z : Z, Commute g (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    π g x ∈ (unitaryFixedSubmodule π Z)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hmap := unitaryFixedSubmodule_map_of_centralizes
    π Z g⁻¹ (fun k => (hg k).inv_left)
  have hzpre : π g⁻¹ z ∈ unitaryFixedSubmodule π Z := by
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  calc
    inner ℂ z (π g x) =
        inner ℂ (π g (π g⁻¹ z)) (π g x) := by simp
    _ = inner ℂ (π g⁻¹ z) x := (π g).inner_map_map (π g⁻¹ z) x
    _ = 0 :=
      (Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) x).mp
        hx (π g⁻¹ z) hzpre
end SoficGroups
