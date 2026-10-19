-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_map_of_centralizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/a27e2217-f5bf-432f-ac78-e9380afe4915

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (g : G)
    (hg : ∀ k : K, Commute g (k : G)) :
    (unitaryFixedSubmodule π K).map (π g).toLinearEquiv.toLinearMap =
      unitaryFixedSubmodule π K := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_unitaryFixedSubmodule]
    intro k
    have hk := (mem_unitaryFixedSubmodule π K x).mp hx k
    calc
      π (k : G) (π g x) = π ((k : G) * g) x := by simp [map_mul]
      _ = π (g * (k : G)) x := by rw [(hg k).eq]
      _ = π g (π (k : G) x) := by simp [map_mul]
      _ = π g x := by rw [hk]
  · intro hz
    refine ⟨π g⁻¹ z, ?_, ?_⟩
    · change π g⁻¹ z ∈ unitaryFixedSubmodule π K
      rw [mem_unitaryFixedSubmodule]
      intro k
      have hk := (mem_unitaryFixedSubmodule π K z).mp hz k
      calc
        π (k : G) (π g⁻¹ z) = π ((k : G) * g⁻¹) z := by simp [map_mul]
        _ = π (g⁻¹ * (k : G)) z := by rw [(hg k).inv_left.eq]
        _ = π g⁻¹ (π (k : G) z) := by simp [map_mul]
        _ = π g⁻¹ z := by rw [hk]
    · simp
end SoficGroups
