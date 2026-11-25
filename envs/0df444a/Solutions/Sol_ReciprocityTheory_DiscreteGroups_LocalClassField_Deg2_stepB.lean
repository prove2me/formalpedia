-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:41.68155+00:00
-- url     : https://prove2.me/submissions/b9bee92e-308b-4f08-b579-d0ec384e0b12

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_s_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_mul_left_of_zero
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)
variable {ρ}
variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)
include hc hrs hr hrn hsn
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (e : G → A) (he0 : ∀ g ∈ N, e g = 0)
    (he : ∀ g, ∀ n ∈ N, c g (g⁻¹ * n * g) = e g - ρ n (e g)) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => ρ (r x) (e (s x))) n g = 0 ∧ c g n - D1 ρ (fun x => ρ (r x) (e (s x))) g n = 0 := by
  have ha0 : ρ (r n) (e (s n)) = 0 := by rw [he0 _ (s_mem hrs hr hn), map_zero]
  constructor
  · simp only [D1]
    rw [hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]
    abel
  · simp only [D1]
    have hconj : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› n hn g
    have h1 : g * n = (g * n * g⁻¹) * g := by group
    have h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g))) := by
      have h3 : c g n = ρ (r g) (c (s g) n) := by
        conv_lhs => rw [← hrs g]
        exact mul_left_of_zero hc h0 _ (hr g) _ _
      have h4 := he (s g) (s g * n * (s g)⁻¹) (Subgroup.Normal.conj_mem ‹_› n hn _)
      have h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n := by group
      rw [h5] at h4
      rw [h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      have key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a := by intros; group
      have key' := key (r g) (s g)
      rw [hrs] at key'
      rw [key']
    rw [ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]
    abel
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
