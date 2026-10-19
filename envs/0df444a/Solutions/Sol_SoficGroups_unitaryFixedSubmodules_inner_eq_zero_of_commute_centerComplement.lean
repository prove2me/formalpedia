-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodules_inner_eq_zero_of_commute_centerComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/364ae21e-cd17-4043-b4bc-42d7f6ce0410

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_sup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_of_commute
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ j : J, Commute (k : G) (j : G))
    (hKZ : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    (hcenter : Z ≤ K ⊔ J)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π K)
    (hb : b ∈ unitaryFixedSubmodule π J)
    (hbZ : b ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    inner ℂ a b = 0 := by
  letI : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  let p : H := (unitaryFixedSubmodule π K).starProjection b
  have hpK : p ∈ unitaryFixedSubmodule π K :=
    Submodule.starProjection_apply_mem _ _
  have hpJ : p ∈ unitaryFixedSubmodule π J :=
    unitaryFixedSubmodule_starProjection_mem_of_commute
      π K J hcomm hb
  have hpJoin : p ∈ unitaryFixedSubmodule π (K ⊔ J) := by
    rw [unitaryFixedSubmodule_sup]
    exact ⟨hpK, hpJ⟩
  have hpZ : p ∈ unitaryFixedSubmodule π Z := by
    rw [mem_unitaryFixedSubmodule]
    intro z
    exact (mem_unitaryFixedSubmodule π (K ⊔ J) p).mp
      hpJoin ⟨z, hcenter z.property⟩
  have hpZorth : p ∈ (unitaryFixedSubmodule π Z)ᗮ :=
    unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
      π K Z hKZ hbZ
  have hpzero : p = 0 := by
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp
      ((Submodule.mem_orthogonal (unitaryFixedSubmodule π Z) p).mp
        hpZorth p hpZ)
  apply inner_eq_zero_symm.mp
  simpa [p, hpzero] using
    (Submodule.starProjection_inner_eq_zero
      (K := unitaryFixedSubmodule π K) b a ha)
end SoficGroups
