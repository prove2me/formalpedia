-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Is_torsor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:25.918489+00:00
-- url     : https://prove2.me/submissions/3377e1ff-4970-4ed8-bc12-b2ccb007fb77

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_lift_cocycle
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
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution (hs : ∀ m n, Function.Surjective ((τ m).f n)) :
    ∀ j m p, p ∈ Is A τ k c j m → ∀ q, q ∈ Is A τ k c j m ↔
      ∃ hx : (A m).d k (q - p) = 0, (Submodule.Quotient.mk ⟨q - p, hx⟩ : (A m).H k) ∈ Hs A τ k j m := by
  intro j
  induction j with
  | zero =>
    intro m p hp q
    have hp' : (A m).d k p = c m := hp
    show (A m).d k q = c m ↔ _
    simp only [Hs, Submodule.mem_top, exists_prop, and_true, map_sub, hp', sub_eq_zero]
  | succ j ih =>
    intro m p hp q
    obtain ⟨p', hp', rfl⟩ := hp
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨hx, hmem⟩ := (ih (m+1) p' hp' q').1 hq'
      have hx' : (A m).d k ((τ m).f k q' - (τ m).f k p') = 0 := by
        rw [← map_sub, ← (τ m).comm, hx, map_zero]
      refine ⟨hx', ?_⟩
      have he : (Submodule.Quotient.mk ⟨(τ m).f k q' - (τ m).f k p', hx'⟩ : (A m).H k) =
          (τ m).H k (Submodule.Quotient.mk ⟨q' - p', hx⟩) := by
        rw [H_mk]; congr 1; exact Subtype.ext (map_sub _ _ _).symm
      rw [he]
      exact Submodule.mem_map_of_mem hmem
    · rintro ⟨hx, hmem⟩
      obtain ⟨h, hh, he⟩ := hmem
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      obtain ⟨y', h1, h2⟩ := lift_cocycle (τ m) (hs m) k y ⟨_, hx⟩ he
      have h2' : (τ m).f k y' = q - (τ m).f k p' := congrArg Subtype.val h2
      refine ⟨p' + y', ?_, ?_⟩
      · rw [ih (m+1) p' hp']
        have hy0 : (A (m+1)).d k (p' + y' - p') = 0 := by rw [add_sub_cancel_left]; exact y'.2
        refine ⟨hy0, ?_⟩
        have : (⟨p' + y' - p', hy0⟩ : (A (m+1)).Z k) = y' := Subtype.ext (add_sub_cancel_left _ _)
        rw [this, h1]; exact hh
      · rw [map_add, h2']; abel
end ReciprocityTheory.Coh.InflationTower
