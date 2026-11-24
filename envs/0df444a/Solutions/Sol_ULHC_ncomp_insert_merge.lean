-- Prove2me | solution 1 for ULHC.ncomp_insert_merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:17.79867+00:00
-- url     : https://prove2.me/submissions/e736c174-f796-4979-a442-be947b4d1ece

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_conn_insert
import Theorems.Thm_ULHC_cls_eq_of_conn
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {e : Edge}
    (hu : e.p ∈ V) (hv : e.q ∈ V) (hn : ¬ Conn F e.p e.q) :
    ncomp V (insert e F) + 1 = ncomp V F := by
  set A := cls V F e.p
  set B := cls V F e.q
  set W := V.filter (fun w => ¬ Conn F e.p w ∧ ¬ Conn F e.q w)
  set Rest := W.image (cls V F)
  -- New classes.
  have cls' : ∀ x ∈ V, cls V (insert e F) x =
      if Conn F e.p x ∨ Conn F e.q x then A ∪ B else cls V F x := by
    intro x hx
    split_ifs with hc
    · ext y
      simp only [cls, A, B, Finset.mem_filter, Finset.mem_union, conn_insert]
      rcases hc with hc | hc
      · constructor
        · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact Or.inl ⟨hy, hc.trans h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
          · exact ⟨hy, Or.inl (hc.symm.trans h)⟩
          · exact ⟨hy, Or.inr (Or.inl ⟨hc.symm, h⟩)⟩
      · constructor
        · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact Or.inr ⟨hy, hc.trans h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
          · exact ⟨hy, Or.inr (Or.inr ⟨hc.symm, h⟩)⟩
          · exact ⟨hy, Or.inl (hc.symm.trans h)⟩
    · simp only [not_or] at hc
      ext y
      simp only [cls, Finset.mem_filter, conn_insert]
      constructor
      · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ⟨hy, h⟩
        · exact absurd h1.symm hc.1
        · exact absurd h1.symm hc.2
      · rintro ⟨hy, h⟩; exact ⟨hy, Or.inl h⟩
  -- Old image and new image in terms of `Rest`.
  have uA : e.p ∈ A := mem_cls_self hu
  have vB : e.q ∈ B := mem_cls_self hv
  have notin : ∀ S ∈ Rest, e.p ∉ S ∧ e.q ∉ S := by
    intro S hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hS
    simp only [W, Finset.mem_filter] at hw
    unfold cls; simp only [Finset.mem_filter, not_and]
    exact ⟨fun _ h => hw.2.1 h.symm, fun _ h => hw.2.2 h.symm⟩
  have hAB : A ≠ B := by
    intro h; apply hn
    have : e.p ∈ B := h ▸ uA
    simp only [B, cls, Finset.mem_filter] at this
    exact this.2.symm
  have old : V.image (cls V F) = insert A (insert B Rest) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_insert, Rest, W, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases h1 : Conn F e.p x
      · exact Or.inl (cls_eq_of_conn h1).symm
      · by_cases h2 : Conn F e.q x
        · exact Or.inr (Or.inl (cls_eq_of_conn h2).symm)
        · exact Or.inr (Or.inr ⟨x, ⟨hx, h1, h2⟩, rfl⟩)
    · rintro (rfl | rfl | ⟨x, ⟨hx, _⟩, rfl⟩)
      · exact ⟨e.p, hu, rfl⟩
      · exact ⟨e.q, hv, rfl⟩
      · exact ⟨x, hx, rfl⟩
  have new : V.image (cls V (insert e F)) = insert (A ∪ B) Rest := by
    ext S
    simp only [Finset.mem_image, Finset.mem_insert, Rest, W, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [cls' x hx]
      split_ifs with h
      · exact Or.inl rfl
      · simp only [not_or] at h; exact Or.inr ⟨x, ⟨hx, h.1, h.2⟩, rfl⟩
    · rintro (rfl | ⟨x, ⟨hx, h1, h2⟩, rfl⟩)
      · refine ⟨e.p, hu, ?_⟩
        rw [cls' _ hu, if_pos (Or.inl (Conn.refl _ _))]
      · refine ⟨x, hx, ?_⟩
        rw [cls' _ hx, if_neg (by simp only [not_or]; exact ⟨h1, h2⟩)]
  unfold ncomp
  rw [old, new]
  have hA : A ∉ insert B Rest := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hAB, fun h => (notin A h).1 uA⟩
  have hB : B ∉ Rest := fun h => (notin B h).2 vB
  have hAB' : A ∪ B ∉ Rest := fun h => (notin _ h).1 (Finset.mem_union_left _ uA)
  rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
    Finset.card_insert_of_notMem hAB']
end ULHC
