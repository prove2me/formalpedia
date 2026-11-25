-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:54:56.650177+00:00
-- url     : https://prove2.me/submissions/30c4b405-5174-4c25-81b8-910e2b91e5f6

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_nHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_eq_card_H0hat
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe


attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]
variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (ρ : Representation ℤ G ℤ) (hρ : ∀ c x, ρ c x = x) (g : G) :
    HFin ρ g ∧ Nat.card (TateZerothCohomology ρ g) = Nat.card G ∧ Subsingleton (H1 ρ g) ∧ h ρ g = Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hD : (dHom ρ g).ker = ⊤ := by
    ext x; simp [AddMonoidHom.mem_ker, hρ]
  have hNx : ∀ x, nHom ρ x = (Nat.card G : ℤ) * x := fun x => by
    rw [nHom_apply]; simp [hρ]
  have hN : (nHom ρ).range = AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    ext x
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
  have h0 : Nat.card (TateZerothCohomology ρ g) = Nat.card G := by
    change ((nHom ρ).range.addSubgroupOf (dHom ρ g).ker).index = _
    change (nHom ρ).range.relIndex (dHom ρ g).ker = _
    rw [hD, AddSubgroup.relIndex_top_right, hN, Int.index_zmultiples]
    simp
  have h1 : Subsingleton (H1 ρ g) := by
    have : Subsingleton (nHom ρ).ker := ⟨fun x y => by
      have hx : nHom ρ x = 0 := x.2
      have hy : nHom ρ y = 0 := y.2
      rw [hNx] at hx hy
      apply Subtype.ext
      have hne : (Nat.card G : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [(mul_eq_zero.1 hx).resolve_left hne, (mul_eq_zero.1 hy).resolve_left hne]⟩
    exact (QuotientAddGroup.mk_surjective).subsingleton
  refine ⟨⟨Nat.finite_of_card_ne_zero (by rw [h0]; exact hpos.ne'), inferInstance⟩, h0, h1, ?_⟩
  rw [h_eq_card_H0hat, h0]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
