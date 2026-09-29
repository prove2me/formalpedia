-- Prove2me | solution 1 for Subgroup.exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/30f1179a-4f3d-598d-8ca5-64fc28010a2c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm

set_option autoImplicit false

theorem solution {G : Type*} [Group G] {V : Type*} [CommGroup V] (π : G →* V) (hZ : π.ker ≤ Subgroup.center G) (hsq : ∀ z ∈ π.ker, ∃ w ∈ π.ker, w * w = z) (H : Subgroup V) (hH : ∀ h ∈ H, h * h = 1) (hlift : ∀ h ∈ H, ∃ g : G, π g = h) (hcomm : ∀ g g' : G, π g ∈ H → π g' ∈ H → g * g' = g' * g) : ∃ K : Subgroup G, (∀ g ∈ K, ∀ g' ∈ K, π g = π g' → g = g') ∧ ∀ v : V, (∃ g ∈ K, π g = v) ↔ v ∈ H := by
  classical

  have hcen : ∀ z ∈ π.ker, ∀ a : G, a * z = z * a := fun z hz a =>
    Subgroup.mem_center_iff.1 (hZ hz) a

  let P : Set (Subgroup G) := {K | (∀ g ∈ K, π g = 1 → g = 1) ∧ ∀ g ∈ K, π g ∈ H}
  have hbot : (⊥ : Subgroup G) ∈ P :=
    ⟨fun g hg _ => Subgroup.mem_bot.1 hg,
      fun g hg => by rw [Subgroup.mem_bot.1 hg, π.map_one]; exact H.one_mem⟩

  obtain ⟨K, hKmax⟩ := zorn_le₀ P (by
    intro c hcP hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, hbot, fun z hz => absurd hz (Set.notMem_empty z)⟩
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro g hg hg1
        obtain ⟨s, hs, hgs⟩ := (Subgroup.mem_sSup_of_directedOn hne hc.directedOn).1 hg
        exact (hcP hs).1 g hgs hg1
      · intro g hg
        obtain ⟨s, hs, hgs⟩ := (Subgroup.mem_sSup_of_directedOn hne hc.directedOn).1 hg
        exact (hcP hs).2 g hgs)
  have hK1 : ∀ g ∈ K, π g = 1 → g = 1 := hKmax.prop.1
  have hyH : ∀ y ∈ K, π y ∈ H := hKmax.prop.2

  have hsurj : ∀ a ∈ H, ∃ g ∈ K, π g = a := by
    intro a haH
    by_contra haL

    obtain ⟨g, hg⟩ := hlift a haH
    have hgg : g * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, π.map_mul, hg, hH a haH]
    obtain ⟨w, hw, hww⟩ := hsq _ hgg
    have hw1 : π w = 1 := (MonoidHom.mem_ker).1 hw
    have hc : w⁻¹ * g = g * w⁻¹ := (Commute.inv_right (hcen w hw g)).eq.symm
    set k : G := g * w⁻¹ with hkdef
    have hk : π k = a := by
      rw [hkdef, π.map_mul, π.map_inv, hw1, inv_one, mul_one, hg]
    have hkk : k * k = 1 := by
      rw [hkdef, mul_assoc, ← mul_assoc w⁻¹ g w⁻¹, hc, mul_assoc g w⁻¹ w⁻¹, ← mul_assoc g g, ← hww]
      group
    have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_left hkk
    have hkH : π k ∈ H := by rw [hk]; exact haH
    have hyk : ∀ y ∈ K, y * k = k * y := fun y hy => hcomm y k (hyH y hy) hkH

    let K' : Subgroup G :=
      { carrier := {x | ∃ y ∈ K, x = y ∨ x = y * k}
        mul_mem' := by
          rintro x x' ⟨y, hy, hx⟩ ⟨y', hy', hx'⟩
          rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> rw [hx, hx']
          · exact ⟨y * y', K.mul_mem hy hy', Or.inl rfl⟩
          · exact ⟨y * y', K.mul_mem hy hy', Or.inr (mul_assoc y y' k).symm⟩
          · exact ⟨y * y', K.mul_mem hy hy', Or.inr (by rw [mul_assoc, ← hyk y' hy', ← mul_assoc])⟩
          · exact ⟨y * y', K.mul_mem hy hy', Or.inl (by
              rw [mul_assoc, ← mul_assoc k y' k, ← hyk y' hy', mul_assoc y' k k, hkk, mul_one])⟩
        one_mem' := ⟨1, K.one_mem, Or.inl rfl⟩
        inv_mem' := by
          rintro x ⟨y, hy, hx | hx⟩ <;> rw [hx]
          · exact ⟨y⁻¹, K.inv_mem hy, Or.inl rfl⟩
          · exact ⟨y⁻¹, K.inv_mem hy, Or.inr (by
              rw [mul_inv_rev, hkinv, ← hyk y⁻¹ (K.inv_mem hy)])⟩ }
    have memK' : ∀ x : G, x ∈ K' ↔ ∃ y ∈ K, x = y ∨ x = y * k := fun x => Iff.rfl
    have hK'P : K' ∈ P := by
      refine ⟨?_, ?_⟩
      ·
        intro x hx hx1
        obtain ⟨y, hy, hx | hx⟩ := (memK' x).1 hx
        · rw [hx] at hx1 ⊢
          exact hK1 y hy hx1
        · exfalso
          apply haL
          rw [hx, π.map_mul, hk] at hx1
          exact ⟨y⁻¹, K.inv_mem hy, by rw [π.map_inv, eq_inv_of_mul_eq_one_right hx1]⟩
      ·
        intro x hx
        obtain ⟨y, hy, hx | hx⟩ := (memK' x).1 hx <;> rw [hx]
        · exact hyH y hy
        · rw [π.map_mul]
          exact H.mul_mem (hyH y hy) hkH
    have hKK' : K ≤ K' := fun y hy => (memK' y).2 ⟨y, hy, Or.inl rfl⟩
    have hkK' : k ∈ K' := (memK' k).2 ⟨1, K.one_mem, Or.inr (one_mul k).symm⟩
    exact haL ⟨k, hKmax.2 hK'P hKK' hkK', hk⟩
  refine ⟨K, ?_, ?_⟩
  · intro g hg g' hg' hgg'
    have h1 : g * g'⁻¹ = 1 :=
      hK1 _ (K.mul_mem hg (K.inv_mem hg')) (by rw [π.map_mul, π.map_inv, hgg', mul_inv_cancel])
    exact mul_inv_eq_one.1 h1
  · intro v
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hyH g hg
    · exact hsurj v

end S_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm
end P2MW
export P2MW.S_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm (solution)
