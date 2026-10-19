-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/e67fcfc5-96ae-4f32-915f-3b735daf4aa9

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
    (π : UnitaryRepresentation G H) (K J : Subgroup G) :
    unitaryFixedSubmodule π (K ⊔ J) =
      unitaryFixedSubmodule π K ⊓ unitaryFixedSubmodule π J := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · change x ∈ unitaryFixedSubmodule π K
      rw [mem_unitaryFixedSubmodule]
      intro k
      exact (mem_unitaryFixedSubmodule π (K ⊔ J) x).mp hx
        ⟨k, Subgroup.mem_sup_left k.property⟩
    · change x ∈ unitaryFixedSubmodule π J
      rw [mem_unitaryFixedSubmodule]
      intro j
      exact (mem_unitaryFixedSubmodule π (K ⊔ J) x).mp hx
        ⟨j, Subgroup.mem_sup_right j.property⟩
  · rintro ⟨hxK, hxJ⟩
    have hK : K ≤ unitaryVectorStabilizer π x := by
      intro k hk
      exact (mem_unitaryFixedSubmodule π K x).mp hxK ⟨k, hk⟩
    have hJ : J ≤ unitaryVectorStabilizer π x := by
      intro j hj
      exact (mem_unitaryFixedSubmodule π J x).mp hxJ ⟨j, hj⟩
    rw [mem_unitaryFixedSubmodule]
    intro g
    exact (sup_le hK hJ) g.property
end SoficGroups
