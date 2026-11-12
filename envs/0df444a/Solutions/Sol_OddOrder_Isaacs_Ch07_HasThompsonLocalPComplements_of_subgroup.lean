-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.HasThompsonLocalPComplements.of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:55:57.058555+00:00
-- url     : https://prove2.me/submissions/ae6f98c2-fec6-47aa-9980-da5aba56c391

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section QuotientCenter

/-- Centers commute with a homomorphism that is injective on the subgroup in question.

This restricted-injectivity form applies both to embeddings into an ambient group and
to quotient maps whose kernel is disjoint from a `p`-subgroup. -/
theorem center_map_subtype_map_of_restrict_injective
    {H : Type*} [Group H] (f : G →* H) {P : Subgroup G}
    (hf : Function.Injective (f.comp P.subtype)) :
    (Subgroup.center ↥(P.map f)).map (P.map f).subtype =
      ((Subgroup.center ↥P).map P.subtype).map f := by
  ext x
  constructor
  · intro hx
    have hx_center := Subgroup.mem_center_map_subtype_iff.mp hx
    obtain ⟨z, hzP, hzx⟩ := hx_center.1
    refine ⟨z, Subgroup.mem_center_map_subtype_iff.mpr ⟨hzP, ?_⟩, hzx⟩
    intro w hw
    have hcomm_f := hx_center.2 (f w) ⟨w, hw, rfl⟩
    rw [← hzx] at hcomm_f
    have hsub :
        (f.comp P.subtype) (⟨w, hw⟩ * ⟨z, hzP⟩) =
          (f.comp P.subtype) (⟨z, hzP⟩ * ⟨w, hw⟩) := by
      change f (w * z) = f (z * w)
      simpa only [map_mul] using hcomm_f
    exact congrArg Subtype.val (hf hsub)
  · rintro ⟨z, hz, rfl⟩
    have hz_center := Subgroup.mem_center_map_subtype_iff.mp hz
    apply Subgroup.mem_center_map_subtype_iff.mpr
    refine ⟨⟨z, hz_center.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg f (hz_center.2 w hw)

end QuotientCenter

section LocalHypothesisTransport

/-- A normal `p`-complement descends along an inclusion of finite subgroups. -/
theorem hasNormalPComplement_of_le
    [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hBA : B ≤ A)
    (hA : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥A) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥B := by
  have hSub := OddOrder.Isaacs.Ch05.hasNormalPComplement_of_subgroup hA
    (B.subgroupOf A)
  exact hasNormalPComplement_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hBA) hSub

/-- A homomorphic image of a normalizer normalizes the image subgroup. -/
theorem map_normalizer_le_normalizer_map
    {A B : Type*} [Group A] [Group B] (f : A →* B) (L : Subgroup A) :
    (Subgroup.normalizer (L : Set A)).map f ≤
      Subgroup.normalizer ((L.map f : Subgroup B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := Subgroup.mem_normalizer_iff.mp hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨x * z * x⁻¹, (hx' z).mp hz, ?_⟩
    simp only [map_mul, map_inv]
  · rintro ⟨z, hz, hz_eq⟩
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · apply (hx' (x⁻¹ * z * x)).mpr
      have heq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
      rwa [heq]
    · calc
        f (x⁻¹ * z * x) = (f x)⁻¹ * f z * f x := by
          simp only [map_mul, map_inv]
        _ = y := by rw [hz_eq]; group

/-- Ambient Thompson local hypotheses descend to a subgroup containing the
same `p`-subgroup, with centers and Thompson subgroups computed internally. -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    {S : Subgroup H}
    (hS : HasThompsonLocalPComplements p (S.map H.subtype)) :
    HasThompsonLocalPComplements p S := by
  have hCenter :
      (Subgroup.center ↥(S.map H.subtype)).map (S.map H.subtype).subtype =
        ((Subgroup.center ↥S).map S.subtype).map H.subtype :=
    center_map_subtype_map_of_restrict_injective H.subtype
      (H.subtype_injective.comp S.subtype_injective)
  have hJ :
      Subgroup.thompsonJ (S.map H.subtype) p =
        (Subgroup.thompsonJ S p).map H.subtype :=
    Subgroup.thompsonJ_map_of_injective H.subtype_injective S p
  constructor
  · have hC_le :
        (Subgroup.centralizer
            (((Subgroup.center ↥S).map S.subtype : Subgroup H) : Set H)).map
              H.subtype ≤
          Subgroup.centralizer
            (((Subgroup.center ↥(S.map H.subtype)).map
              (S.map H.subtype).subtype : Subgroup G) : Set G) := by
      rw [hCenter]
      simpa only [Subgroup.coe_map] using
        (Subgroup.map_centralizer_le_centralizer_image
          (((Subgroup.center ↥S).map S.subtype : Subgroup H) : Set H) H.subtype)
    have hImage := hasNormalPComplement_of_le hC_le hS.1
    exact hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm hImage
  · have hN_le :
        (Subgroup.normalizer
            ((Subgroup.thompsonJ S p : Subgroup H) : Set H)).map H.subtype ≤
          Subgroup.normalizer
            ((Subgroup.thompsonJ (S.map H.subtype) p : Subgroup G) : Set G) := by
      rw [hJ]
      exact map_normalizer_le_normalizer_map H.subtype _
    have hImage := hasNormalPComplement_of_le hN_le hS.2
    exact hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm hImage

end LocalHypothesisTransport

end OddOrder.Isaacs.Ch07
