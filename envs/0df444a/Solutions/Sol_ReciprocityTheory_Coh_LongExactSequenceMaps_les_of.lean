-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.les_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:50.182625+00:00
-- url     : https://prove2.me/submissions/9420f826-79a6-4371-bad1-5e1359a6aa0d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_eq
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
open ReciprocityTheory.Coh.LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)
namespace ReciprocityTheory.Coh.LongExactSequenceMaps
theorem _root_.solution (hs : SES i p) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ) :
    LES i p δ where
  inj := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨x, hx, rfl⟩ := cls_surj A 0 h
    rw [H_cls, cls_eq_zero, mem_B_zero] at hh
    rw [cls_eq_zero, mem_B_zero]
    exact hs.inj 0 (hh.trans (map_zero _).symm)
  exB n := by
    intro y
    obtain ⟨b, hb, rfl⟩ := cls_surj B n y
    constructor
    · intro h
      rw [H_cls, cls_eq_zero] at h
      cases n with
      | zero =>
        rw [mem_B_zero] at h
        obtain ⟨a, ha⟩ := ((hs.exact 0) _).1 h
        have da : A.d 0 a = 0 := hs.inj 1 (by rw [i.comm, ha, hb, map_zero])
        exact ⟨A.cls 0 a da, by rw [H_cls]; exact cls_congr _ _ _ _ _ _ ha⟩
      | succ m =>
        rw [mem_B_succ] at h
        obtain ⟨c', hc'⟩ := h
        obtain ⟨b', rfl⟩ := hs.surj m c'
        have h0 : p.f (m + 1) (b - B.d m b') = 0 := by
          rw [map_sub, p.comm, hc', sub_self]
        obtain ⟨a, ha⟩ := ((hs.exact (m + 1)) _).1 h0
        have da : A.d (m + 1) a = 0 :=
          hs.inj (m + 2) (by rw [i.comm, ha, map_sub, hb, B.dd, sub_zero, map_zero])
        refine ⟨A.cls (m + 1) a da, ?_⟩
        rw [H_cls, cls_eq, mem_B_succ]
        exact ⟨-b', by rw [map_neg, ha]; abel⟩
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := cls_surj A n x
      rw [← hx, H_cls, H_cls, cls_eq_zero, p_i i p hs]
      exact Submodule.zero_mem _
  exC n := by
    intro y
    obtain ⟨b, a, hc, ha, hb, rfl⟩ := rep i p hs n y
    constructor
    · intro h
      rw [hδ n b a hc ha hb, cls_eq_zero, mem_B_succ] at h
      obtain ⟨a', ha'⟩ := h
      have hz : B.d n (b - i.f n a') = 0 := by
        rw [map_sub, hb, ← i.comm, ha', sub_self]
      refine ⟨B.cls n (b - i.f n a') hz, ?_⟩
      rw [H_cls]
      exact cls_congr _ _ _ _ _ _ (by rw [map_sub, p_i i p hs, sub_zero])
    · rintro ⟨x, hx⟩
      obtain ⟨b'', hb'', rfl⟩ := cls_surj B n x
      rw [← hx, H_cls, hδ n b'' 0 _ (map_zero _) (by rw [hb'', map_zero]), cls_eq_zero]
      exact Submodule.zero_mem _
  exA n := by
    intro y
    obtain ⟨a, ha, rfl⟩ := cls_surj A (n + 1) y
    rw [H_cls, cls_eq_zero, mem_B_succ]
    constructor
    · rintro ⟨b, hb⟩
      have hc : C.d n (p.f n b) = 0 := by rw [← p.comm, hb, p_i i p hs]
      exact ⟨C.cls n (p.f n b) hc, hδ n b a hc ha hb⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, a', hc, ha', hb, rfl⟩ := rep i p hs n x
      rw [hδ n b a' hc ha' hb, cls_eq, mem_B_succ] at hx
      obtain ⟨z, hz⟩ := hx
      refine ⟨b - i.f n z, ?_⟩
      rw [map_sub, hb, ← i.comm, hz, map_sub, sub_sub_cancel]
end ReciprocityTheory.Coh.LongExactSequenceMaps
