-- Prove2me | solution 1 for Subgroup.nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b2ea5644-5577-5102-b21c-43ca72a7df3e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff

set_option autoImplicit false

theorem solution
    {U G : Type*} [CommGroup U] [Group G] [Finite U]
    (Ψ : U →* G) (hΨ : Function.Surjective Ψ)
    (c : U) (hc : Ψ c = 1) (hcard : Nat.card G = (Subgroup.zpowers c).index)
    (H : Subgroup U) (hcH : c ∈ H) (I : Subgroup G) (hI : ∀ u : U, Ψ u ∈ I ↔ u ∈ H) :
    Nonempty (↥H ⧸ Subgroup.zpowers (⟨c, hcH⟩ : ↥H) ≃* ↥I) := by
  classical

  have hle : Subgroup.zpowers c ≤ Ψ.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact hc
  have hidx : Ψ.ker.index = (Subgroup.zpowers c).index := by
    rw [← hcard, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΨ, Subgroup.card_top]
  have hker : Ψ.ker = Subgroup.zpowers c := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := Ψ.ker.card_mul_index
    have h2 := (Subgroup.zpowers c).card_mul_index
    have hne : (Subgroup.zpowers c).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    have : Nat.card ↥Ψ.ker = Nat.card ↥(Subgroup.zpowers c) :=
      Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)
    exact this.le

  let ψH : ↥H →* ↥I := (Ψ.domRestrict H).codRestrict I (fun h => (hI h).mpr h.2)
  have hψH : ∀ h : ↥H, ((ψH h : ↥I) : G) = Ψ (h : U) := fun _ => rfl
  have hsurj : Function.Surjective ψH := by
    intro i
    obtain ⟨u, hu⟩ := hΨ (i : G)
    have huH : u ∈ H := (hI u).mp (by rw [hu]; exact i.2)
    exact ⟨⟨u, huH⟩, Subtype.ext (by rw [hψH]; exact hu)⟩
  have hkerH : ψH.ker = Subgroup.zpowers (⟨c, hcH⟩ : ↥H) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      have hxU : (x : U) ∈ Ψ.ker := by
        rw [MonoidHom.mem_ker, ← hψH, hx]; rfl
      rw [hker, Subgroup.mem_zpowers_iff] at hxU
      obtain ⟨k, hk⟩ := hxU
      exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)⟩
    · rintro ⟨k, hk⟩
      apply Subtype.ext
      rw [hψH]
      have : ((⟨c, hcH⟩ : ↥H) ^ k : ↥H) = x := hk
      rw [← this, SubgroupClass.coe_zpow, map_zpow, hc, one_zpow]
      rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerH.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψH hsurj)⟩

end S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff
end P2MW
export P2MW.S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff (solution)
