-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:10.563165+00:00
-- url     : https://prove2.me/submissions/82e4007b-e7a3-440d-9ec7-f5468418012a

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L))
    (f : H → Lˣ) (E : IntermediateField K L) [FiniteDimensional K E]
    (hE : ∀ h : H, (h : L ≃ₐ[K] L) ∈ E.fixingSubgroup → f h = 1)
    (hc : ∀ g h : H, f (g * h) = f g * Units.map ((g : L ≃ₐ[K] L) : L →* L) (f h)) :
    ∃ β : Lˣ, ∀ h : H, f h = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  classical

  let r : H → (E →ₐ[K] L) := fun h => ((h : L ≃ₐ[K] L) : L →ₐ[K] L).comp E.val
  have hr : ∀ (h : H) (x : E), r h x = (h : L ≃ₐ[K] L) (x : L) := fun _ _ => rfl
  have hfr : ∀ g h : H, r g = r h → f g = f h := by
    intro g h hgh
    have hmem : ((g⁻¹ * h : H) : L ≃ₐ[K] L) ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x := DFunLike.congr_fun hgh ⟨x, hx⟩
      show ((g : L ≃ₐ[K] L)⁻¹ * (h : L ≃ₐ[K] L)) x = x
      rw [AlgEquiv.mul_apply, ← h1]
      exact (g : L ≃ₐ[K] L).symm_apply_apply x
    have h2 := hc g (g⁻¹ * h)
    rw [mul_inv_cancel_left, hE _ hmem, map_one, mul_one] at h2
    exact h2.symm
  let S := Set.range r
  have : Finite (E →ₐ[K] L) := inferInstance
  let _ : Fintype S := Fintype.ofFinite S
  have hrep : ∀ s : S, ∃ h : H, r h = s.1 := fun s => s.2
  choose rep hrep using hrep
  let a : S → L := fun s => (f (rep s) : L)
  have hli : LinearIndependent L (fun s : S => ((s.1 : E →* L) : E → L)) := by
    refine (linearIndependent_monoidHom E L).comp (fun s : S => (s.1 : E →* L)) ?_
    intro s t hst
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hst x
  have hex : ∃ c : E, ∑ s : S, a s * s.1 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ s : S, a s • ((s.1 : E →* L) : E → L) = 0 := by
      funext c
      rw [Finset.sum_apply]
      exact hcon c
    have := Fintype.linearIndependent_iff.1 hli a h0 ⟨r 1, 1, rfl⟩
    exact (f (rep ⟨r 1, 1, rfl⟩)).ne_zero this
  obtain ⟨c, hcne⟩ := hex
  set b : L := ∑ s : S, a s * s.1 c with hb
  have key : ∀ h : H, b = f h * (h : L ≃ₐ[K] L) b := by
    intro h
    let m : S → S := fun s => ⟨r (h * rep s), _, rfl⟩
    have hm1 : ∀ (s : S) (x : E), (m s).1 x = (h : L ≃ₐ[K] L) (s.1 x) := by
      intro s x
      show r (h * rep s) x = _
      rw [← hrep s, hr, hr]
      rfl
    have hminj : Function.Injective m := by
      intro s t hst
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      apply (h : L ≃ₐ[K] L).injective
      rw [← hm1, ← hm1, hst]
    have hmbij : Function.Bijective m := Finite.injective_iff_bijective.1 hminj
    have hma : ∀ s, a (m s) = f h * (h : L ≃ₐ[K] L) (a s) := by
      intro s
      show (f (rep (m s)) : L) = _
      rw [hfr (rep (m s)) (h * rep s) (hrep (m s)), hc]
      rfl
    calc b = ∑ s, a (m s) * (m s).1 c := (hmbij.sum_comp (fun s => a s * s.1 c)).symm
      _ = f h * (h : L ≃ₐ[K] L) b := by
        rw [hb, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hma, hm1, map_mul, mul_assoc]
  refine ⟨(Units.mk0 b hcne)⁻¹, fun h => ?_⟩
  apply Units.ext
  have hb' : (h : L ≃ₐ[K] L) b ≠ 0 := by
    simpa using hcne
  have e1 : ((Units.map ((h : L ≃ₐ[K] L) : L →* L) (Units.mk0 b hcne)⁻¹ / (Units.mk0 b hcne)⁻¹ : Lˣ) : L)
      = ((h : L ≃ₐ[K] L) b)⁻¹ * b := by
    rw [map_inv, div_inv_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  rw [e1]
  field_simp
  exact (key h).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
