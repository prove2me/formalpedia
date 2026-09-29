-- Prove2me | solution 1 for Subgroup.exists_eq_mul_of_index_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3cdb8f40-2ef3-5d7e-b604-54ad8754f086

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_eq_mul_of_index_inf_eq

open MulAction

namespace S11Orbit2

variable {G : Type*} [Group G]

theorem stabilizer_mk_one_eq (H₁ H₂ : Subgroup G) :
    stabilizer H₂ ((1 : G) : G ⧸ H₁) = H₁.subgroupOf H₂ := by
  ext h
  have key : h • ((1 : G) : G ⧸ H₁) = (((h : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, key, mul_one, QuotientGroup.eq, mul_one,
    inv_mem_iff]

theorem exists_eq_mul_of_index_inf_eq [Finite G] (H₁ H₂ : Subgroup G)
    (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by

  have hrel : H₁.relIndex H₂ = H₁.index := by
    have h1 : H₁.relIndex H₂ * H₂.index = (H₁ ⊓ H₂).index := by
      rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex_mul_index inf_le_right]
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hcard : (orbit H₂ ((1 : G) : G ⧸ H₁)).ncard = (Set.univ : Set (G ⧸ H₁)).ncard := by
    rw [← index_stabilizer, stabilizer_mk_one_eq, Set.ncard_univ, ← Subgroup.index_eq_card]
    exact hrel
  have huniv : orbit H₂ ((1 : G) : G ⧸ H₁) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hcard.ge Set.finite_univ
  have hmem : ((g⁻¹ : G) : G ⧸ H₁) ∈ orbit H₂ ((1 : G) : G ⧸ H₁) := huniv ▸ Set.mem_univ _
  obtain ⟨h₂, hh₂⟩ := mem_orbit_iff.mp hmem
  have key : h₂ • ((1 : G) : G ⧸ H₁) = (((h₂ : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [key, mul_one, QuotientGroup.eq] at hh₂

  refine ⟨g * h₂, ?_, (h₂ : G)⁻¹, H₂.inv_mem h₂.2, by group⟩
  have := H₁.inv_mem hh₂
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

end S11Orbit2

theorem solution {G : Type*} [Group G] [Finite G] (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ :=
  S11Orbit2.exists_eq_mul_of_index_inf_eq H₁ H₂ h g

end S_Subgroup_exists_eq_mul_of_index_inf_eq
end P2MW
export P2MW.S_Subgroup_exists_eq_mul_of_index_inf_eq (solution)
