-- Prove2me | solution 1 for Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5f172e34-c37d-59df-9a47-f0594e1e3df5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq

set_option autoImplicit false

theorem solution
    {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    (K ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex K =
      Nat.card {c : G ⧸ K // ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by
  classical

  have horb : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K) : Set (G ⧸ K)) =
      {c : G ⧸ K | ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by
    ext c
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hstab : (K ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf K =
      MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨-, x, hx, hxk⟩
      show (QuotientGroup.mk ((k : G) * g) : G ⧸ K) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (k : G) = g * x * g⁻¹ := by rw [← hxk]; rfl
      rw [this]
      simpa [mul_assoc] using K.inv_mem hx
    · intro h
      have h' : (QuotientGroup.mk ((k : G) * g) : G ⧸ K) = QuotientGroup.mk g := h
      rw [QuotientGroup.eq] at h'
      refine ⟨k.2, g⁻¹ * k * g, ?_, ?_⟩
      · have := K.inv_mem h'
        simpa [mul_assoc] using this
      · show g * (g⁻¹ * k * g) * g⁻¹ = k
        group
  rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer, horb, Set.ncard_def]
  rfl

end S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
end P2MW
export P2MW.S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq (solution)
