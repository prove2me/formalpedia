-- Prove2me | solution 1 for ValuationSubring.exists_le_and_le_toLocalSubring_of_toSubring_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/39019e9c-fe5c-5dc4-91ad-3e981bd4923e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le

set_option autoImplicit false

universe u

open IsLocalRing

namespace E150V1

variable {K : Type u} [Field K]

theorem inv_mem_of_isUnit {S : Type*} [SetLike S K] [SubringClass S K] (s : S) {x : K} (hx : x ∈ s)
    (h : IsUnit (⟨x, hx⟩ : s)) : x⁻¹ ∈ s := by
  obtain ⟨u, hu⟩ := h
  have hmul : x * ((u⁻¹ : (↥s)ˣ) : s) = 1 := by
    have h1 : ((u : s) * (u⁻¹ : (↥s)ˣ) : s) = 1 := Units.mul_inv u
    have h2 := congrArg (fun t : s => (t : K)) h1
    rw [hu] at h2
    simpa using h2
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact ((u⁻¹ : (↥s)ˣ) : s).2

theorem isUnit_of_inv_mem {S : Type*} [SetLike S K] [SubringClass S K] (s : S) {x : K} (hx : x ∈ s)
    (hx' : x⁻¹ ∈ s) (hx0 : x ≠ 0) : IsUnit (⟨x, hx⟩ : s) := by
  refine ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hx'⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

private def _root_.E150V1.comp (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) : ValuationSubring K where
  carrier := {x | ∃ h : x ∈ O, residue O ⟨x, h⟩ ∈ W}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (⟨a * b, mul_mem ha hb⟩ : O) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul]
    exact mul_mem ha' hb'
  one_mem' := by
    refine ⟨one_mem O, ?_⟩
    have e : (⟨1, one_mem O⟩ : O) = 1 := rfl
    rw [e, map_one]
    exact one_mem W
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    have e : (⟨a + b, add_mem ha hb⟩ : O) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add]
    exact add_mem ha' hb'
  zero_mem' := by
    refine ⟨zero_mem O, ?_⟩
    have e : (⟨0, zero_mem O⟩ : O) = 0 := rfl
    rw [e, map_zero]
    exact zero_mem W
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨neg_mem ha, ?_⟩
    have e : (⟨-a, neg_mem ha⟩ : O) = -⟨a, ha⟩ := rfl
    rw [e, map_neg]
    exact neg_mem ha'
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ O
    · by_cases hx' : residue O ⟨x, hx⟩ ∈ W
      · exact Or.inl ⟨hx, hx'⟩
      · right
        have hx0 : residue O ⟨x, hx⟩ ≠ 0 := fun h => hx' (h ▸ W.zero_mem)
        have hunit : IsUnit (⟨x, hx⟩ : O) := (residue_ne_zero_iff_isUnit _).mp hx0
        have hinv : x⁻¹ ∈ O := inv_mem_of_isUnit O hx hunit
        refine ⟨hinv, ?_⟩
        have hprod : residue O ⟨x, hx⟩ * residue O ⟨x⁻¹, hinv⟩ = 1 := by
          rw [← map_mul]
          have hxK : x ≠ 0 := by
            rintro rfl
            apply hx0
            have e : (⟨(0 : K), hx⟩ : O) = 0 := rfl
            rw [e, map_zero]
          have : (⟨x, hx⟩ : O) * ⟨x⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hxK)
          rw [this, map_one]
        have heq : residue O ⟨x⁻¹, hinv⟩ = (residue O ⟨x, hx⟩)⁻¹ :=
          (inv_eq_of_mul_eq_one_right hprod).symm
        rw [heq]
        exact ((W.mem_or_inv_mem _).resolve_left hx')
    · right
      have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      refine ⟨hinv, ?_⟩
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : O) := by
        intro hu
        have := inv_mem_of_isUnit O hinv hu
        rw [inv_inv] at this
        exact hx this
      have : residue O ⟨x⁻¹, hinv⟩ = 0 := by
        rw [residue_eq_zero_iff]
        exact hnu
      rw [this]; exact W.zero_mem

p2m_export "E150V1" "comp"
theorem comp_le (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) : comp O W ≤ O :=
  fun _ ⟨h, _⟩ => h

theorem mem_comp_iff (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) (x : K) :
    x ∈ comp O W ↔ ∃ h : x ∈ O, residue O ⟨x, h⟩ ∈ W := Iff.rfl

end E150V1

open E150V1 in
theorem solution
    {K : Type u} [Field K] (O : ValuationSubring K) (R : LocalSubring K)
    (hRO : R.toSubring ≤ O.toSubring) :
    ∃ V : ValuationSubring K, V ≤ O ∧ R ≤ V.toLocalSubring := by
  haveI := R.isLocalRing

  let g : R.toSubring →+* O := (R.toSubring.subtype).codRestrict O (fun r => hRO r.2)
  let f : R.toSubring →+* ResidueField O := (residue O).comp g
  let R' : LocalSubring (ResidueField O) := LocalSubring.range f
  obtain ⟨W, hW⟩ := R'.exists_le_valuationSubring
  obtain ⟨hW₁, hW₂⟩ := hW
  refine ⟨comp O W, comp_le O W, ?_⟩
  have hsub : R.toSubring ≤ (comp O W).toLocalSubring.toSubring := by
    intro x hx
    refine ⟨hRO hx, ?_⟩
    have : residue O ⟨x, hRO hx⟩ = f ⟨x, hx⟩ := rfl
    rw [this]
    exact hW₁ (show f ⟨x, hx⟩ ∈ Set.range (⇑(residue O) ∘ ⇑g) from ⟨⟨x, hx⟩, rfl⟩)
  refine ⟨hsub, ⟨?_⟩⟩
  intro a ha

  have haV : (a : K) ∈ comp O W := hsub a.2
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply not_isUnit_zero (M₀ := ↥(comp O W).toLocalSubring.toSubring)
    convert ha
    all_goals first | (with_reducible_and_instances rfl) | skip
    first | exact Subtype.ext h.symm | (apply Subtype.ext; simpa using h.symm)
  have hainvV : (a : K)⁻¹ ∈ comp O W := inv_mem_of_isUnit ((comp O W).toLocalSubring.toSubring) haV ha
  obtain ⟨haO, haW⟩ := (mem_comp_iff O W _).mp haV
  obtain ⟨hainvO, hainvW⟩ := (mem_comp_iff O W _).mp hainvV

  have hfa : f a = residue O ⟨(a : K), haO⟩ := rfl
  have hprod : residue O ⟨(a : K), haO⟩ * residue O ⟨(a : K)⁻¹, hainvO⟩ = 1 := by
    rw [← map_mul]
    have : (⟨(a : K), haO⟩ : O) * ⟨(a : K)⁻¹, hainvO⟩ = 1 := Subtype.ext (mul_inv_cancel₀ ha0)
    rw [this, map_one]
  have hfa0 : f a ≠ 0 := by
    rw [hfa]; intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
  have hfaR' : f a ∈ R'.toSubring := show f a ∈ Set.range (⇑(residue O) ∘ ⇑g) from ⟨a, rfl⟩
  have hunitW : IsUnit (⟨f a, hW₁ hfaR'⟩ : W.toLocalSubring.toSubring) := by
    apply isUnit_of_inv_mem (W.toLocalSubring.toSubring) (hW₁ hfaR') _ hfa0
    have : (f a)⁻¹ = residue O ⟨(a : K)⁻¹, hainvO⟩ := by
      rw [hfa]; exact inv_eq_of_mul_eq_one_right hprod
    rw [this]; exact hainvW

  have hunitR' : IsUnit (⟨f a, hfaR'⟩ : R'.toSubring) := by
    have := hW₂.map_nonunit ⟨f a, hfaR'⟩ (by convert hunitW using 1; exact Subtype.ext rfl)
    exact this

  obtain ⟨c, hc⟩ := hunitR'.exists_right_inv
  obtain ⟨c, hc'⟩ := c
  have hcr : c ∈ Set.range (⇑(residue O) ∘ ⇑g) := hc'
  obtain ⟨b, hb⟩ := hcr
  have hab : f (a * b) = 1 := by
    rw [map_mul]
    change f a * ((⇑(residue O) ∘ ⇑g) b) = 1
    rw [hb]
    exact congrArg Subtype.val hc

  have hm : g (a * b) - 1 ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, map_one]
    change f (a * b) - 1 = 0
    rw [hab, sub_self]
  have hnu : ¬ IsUnit (a * b - 1) := by
    intro hu
    have hu' := hu.map g
    rw [map_sub, map_one] at hu'
    exact absurd hu' hm
  have hmR : 1 - a * b ∈ maximalIdeal R.toSubring := by
    rw [← neg_sub]; exact (maximalIdeal R.toSubring).neg_mem hnu
  have habu : IsUnit (a * b) := isUnit_of_mem_nonunits_one_sub_self _ hmR
  exact isUnit_of_mul_isUnit_left habu

end S_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le
end P2MW
export P2MW.S_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le (solution)
