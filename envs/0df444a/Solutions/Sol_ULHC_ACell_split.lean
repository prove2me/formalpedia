-- Prove2me | solution 1 for ULHC.ACell.split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:08.811804+00:00
-- url     : https://prove2.me/submissions/7f922f32-24aa-44bf-bdea-da168cf947e0

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_insert_conn
import Theorems.Thm_ULHC_Ends_conn_insert_iff
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_Ends_deg_erase
import Theorems.Thm_ULHC_Ends_erase_conn
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_ACell_dk
import Theorems.Thm_ULHC_ACell_e2_ne_e1
import Theorems.Thm_ULHC_ACell_merge
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_class_parity
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_closed_conn
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_leaves_le_two
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_ncomp_congr
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside V F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hl1 : C.l1 ∉ F) (hl2 : C.l2 ∉ F)
  (hdeg2 : ∀ z, (Conn F C.a z ∨ Conn F C.d z) → deg F z = 2)
include hV hVa hVb hVd hVk he1 he2 hl1 hl2 hdeg2
omit hl2
namespace ULHC
namespace ACell
theorem _root_.solution (hy : Conn F C.a C.d) (hle : ∀ z, deg F z ≤ 2)
    (hplanar : ∀ G : Finset Edge, C.e1 ∉ G → C.l1 ∉ G → Conn G C.b C.d → Conn G C.k C.a →
      ¬ Conn G C.a C.b → False) :
    ncomp V (C.res F) = ncomp V F + 1 ∧ (∀ u v, Conn (C.res F) u v → Conn F u v) ∧
      ∀ u v, Conn F u v ↔ Conn (C.res F) u v ∨ (Conn (C.res F) u C.a ∧ Conn (C.res F) C.b v) ∨
        (Conn (C.res F) u C.b ∧ Conn (C.res F) C.a v) := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have hab : Conn G1 C.a C.b :=
    C.h1.erase_conn hV he1 (fun z _ hz => by rw [hdeg2 z (Or.inl hz)]; exact even_two)
  have e1 : ncomp V G1 = ncomp V F := by
    conv_rhs => rw [← Finset.insert_erase he1]
    apply ncomp_congr; intro u _ v _; exact (C.h1.insert_conn hab u v).symm
  have he2' : C.e2 ∈ G1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  set G := G1.erase C.e2 with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have hVG : Inside V G := hV.mono hGF
  have he1G : C.e1 ∉ G := fun h => by simp [G, G1] at h
  have hl1G : C.l1 ∉ G := fun h => hl1 (hGF h)
  set S : Finset Pt := {C.a, C.b, C.d, C.k} with hS
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have degG : ∀ z, Conn F C.a z → deg G z = if z ∈ S then 1 else 2 := by
    intro z hz
    have hz2 := hdeg2 z (Or.inl hz)
    have f1 := C.h1.deg_erase he1 z
    have f2 := C.h2.deg_erase he2' z
    rw [← hG1] at f1
    rw [← hG] at f2
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    by_cases za : z = C.a
    · subst za
      rw [if_pos (Or.inl rfl)] at f1
      rw [if_neg (by rintro (h | h); exact C.ad h; exact C.ak h)] at f2
      rw [if_pos (Or.inl rfl)]; omega
    by_cases zb : z = C.b
    · subst zb
      rw [if_pos (Or.inr rfl)] at f1
      rw [if_neg (by rintro (h | h); exact C.bd h; exact C.bk h)] at f2
      rw [if_pos (Or.inr (Or.inl rfl))]; omega
    rw [if_neg (by rintro (h | h); exact za h; exact zb h)] at f1
    by_cases zd : z = C.d
    · subst zd
      rw [if_pos (Or.inl rfl)] at f2
      rw [if_pos (Or.inr (Or.inr (Or.inl rfl)))]; omega
    by_cases zk : z = C.k
    · subst zk
      rw [if_pos (Or.inr rfl)] at f2
      rw [if_pos (Or.inr (Or.inr (Or.inr rfl)))]; omega
    rw [if_neg (by rintro (h | h); exact zd h; exact zk h)] at f2
    rw [if_neg (by rintro (h | h | h | h) <;> contradiction)]; omega
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    have f1 := C.h1.deg_erase he1 z
    have f2 := C.h2.deg_erase he2' z
    rw [← hG1] at f1
    rw [← hG] at f2
    have := hle z
    omega
  have mem_cls : ∀ u w, w ∈ cls V G u ↔ w ∈ V ∧ Conn G u w := by
    intro u w; simp [cls]
  have cnt : ∀ K : Finset Pt, ((K ∩ S).card : ℕ) =
      (if C.a ∈ K then 1 else 0) + (if C.b ∈ K then 1 else 0) + (if C.d ∈ K then 1 else 0) +
        (if C.k ∈ K then 1 else 0) := by
    intro K
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [hS, Finset.sum_insert (by simp [C.ab, C.ad, C.ak]),
      Finset.sum_insert (by simp [C.bd, C.bk]),
      Finset.sum_insert (by simp [C.dk]), Finset.sum_singleton]
    ring
  have par : ∀ u, Conn F C.a u → Even ((cls V G u ∩ S).card) := by
    intro u hu
    apply class_parity hVG u S
    intro z hz
    rw [mem_cls] at hz
    exact degG z (hu.trans (hz.2.mono hGF))
  have leaf : ∀ u, Conn F C.a u → (cls V G u ∩ S).card ≤ 2 := by
    intro u hu
    have hl2 := leaves_le_two (V := V) _ G rfl hVG hleG u
    refine le_trans (Finset.card_le_card ?_) hl2
    intro z hz
    rw [Finset.mem_inter, mem_cls] at hz
    rw [Finset.mem_filter]
    refine ⟨hz.1.1, hz.1.2, ?_⟩
    rw [degG z (hu.trans (hz.1.2.mono hGF)), if_pos hz.2]
  have aK : C.a ∈ cls V G C.a := mem_cls_self hVa
  have bK : C.b ∈ cls V G C.b := mem_cls_self hVb
  have pa := par C.a (Conn.refl _ _)
  have la := leaf C.a (Conn.refl _ _)
  have pb := par C.b hFab
  rw [cnt] at pa la pb
  rw [if_pos aK] at pa la
  rw [if_pos bK] at pb
  by_cases hbA : C.b ∈ cls V G C.a
  · exfalso
    rw [if_pos hbA] at la pa
    have hdA : C.d ∉ cls V G C.a := by intro h; rw [if_pos h] at la; split_ifs at la <;> omega
    have hkA : C.k ∉ cls V G C.a := by intro h; rw [if_pos h] at la; split_ifs at la; omega
    have hcl : Closed F (cls V G C.a) := by
      intro u hu w huw
      obtain ⟨f, hf, hfw⟩ := huw
      have hw : Ends f u w := by
        rcases hfw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      by_cases hfb : f = C.e1
      · subst hfb
        have hw' := (C.h1.inc_iff w).1 ((hw.inc_iff w).2 (Or.inr rfl))
        rcases hw' with rfl | rfl
        · exact aK
        · exact hbA
      by_cases hft : f = C.e2
      · subst hft
        have hu' := (C.h2.inc_iff u).1 ((hw.inc_iff u).2 (Or.inl rfl))
        rcases hu' with rfl | rfl
        · exact absurd hu hdA
        · exact absurd hu hkA
      · exact closed_cls hVG C.a u hu w
          ⟨f, Finset.mem_erase.2 ⟨hft, Finset.mem_erase.2 ⟨hfb, hf⟩⟩, hfw⟩
    exact hdA (closed_conn hcl aK hy)
  rw [if_neg hbA] at la pa
  have hAB : ∀ w, w ∈ cls V G C.a → w ∉ cls V G C.b := by
    intro w hwa hwb
    apply hbA
    rw [mem_cls] at hwa hwb ⊢
    exact ⟨hVb, hwa.2.trans hwb.2.symm⟩
  have haB : C.a ∉ cls V G C.b := fun h => hAB C.a aK h
  rw [if_neg haB] at pb
  by_cases hkA : C.k ∈ cls V G C.a
  · exfalso
    have hkB : C.k ∉ cls V G C.b := hAB C.k hkA
    rw [if_neg hkB] at pb
    have hdB : C.d ∈ cls V G C.b := by
      by_contra h; rw [if_neg h] at pb; simp at pb
    apply hplanar G he1G hl1G
    · exact ((mem_cls _ _).1 hdB).2
    · exact ((mem_cls _ _).1 hkA).2.symm
    · intro h; exact hbA ((mem_cls _ _).2 ⟨hVb, h⟩)
  · rw [if_neg hkA] at la pa
    have hdA : C.d ∈ cls V G C.a := by
      by_contra h; rw [if_neg h] at pa; simp at pa
    have hdB : C.d ∉ cls V G C.b := hAB C.d hdA
    rw [if_neg hdB] at pb
    have hkB : C.k ∈ cls V G C.b := by
      by_contra h; rw [if_neg h] at pb; simp at pb
    have hGad : Conn G C.a C.d := ((mem_cls _ _).1 hdA).2
    have hGbk : Conn G C.b C.k := ((mem_cls _ _).1 hkB).2
    have hGdk : ¬ Conn G C.d C.k := by
      intro h; exact hkA ((mem_cls _ _).2 ⟨hVk, hGad.trans h⟩)
    have em : ncomp V G1 + 1 = ncomp V G := by
      have := C.h2.merge (V := V) (F := G) hVd hVk hGdk
      rw [Finset.insert_erase he2'] at this
      exact this
    have s1 : G ⊆ insert C.l1 G := Finset.subset_insert _ _
    have cl : ∀ u v, Conn (insert C.l1 G) u v ↔ Conn G u v := C.h3.insert_conn hGad
    have cr : ∀ u v, Conn (C.res F) u v ↔ Conn (insert C.l1 G) u v :=
      C.h4.insert_conn (hGbk.mono s1)
    have el : ncomp V (insert C.l1 G) = ncomp V G := by
      apply ncomp_congr; intro u _ v _; exact cl u v
    have er : ncomp V (C.res F) = ncomp V (insert C.l1 G) := by
      apply ncomp_congr; intro u _ v _; exact cr u v
    have cRG : ∀ u v, Conn (C.res F) u v ↔ Conn G u v := fun u v => (cr u v).trans (cl u v)
    refine ⟨by rw [er, el]; omega, fun u v h => ((cRG u v).1 h).mono hGF, fun u v => ?_⟩
    -- `F` has the connections of `G1 = G + e2`, with `e2 = d–k`, `a ~ d`, `b ~ k` in `G`.
    have cG1 : ∀ u v, Conn G1 u v ↔ Conn F u v := by
      intro u v
      have := C.h1.insert_conn hab u v
      rw [Finset.insert_erase he1] at this; exact this.symm
    rw [← cG1, ← Finset.insert_erase he2', C.h2.conn_insert_iff, cRG, cRG, cRG, cRG, cRG]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1.trans hGad.symm, hGbk.trans h2⟩)
      · exact Or.inr (Or.inr ⟨h1.trans hGbk.symm, hGad.trans h2⟩)
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1.trans hGad, hGbk.symm.trans h2⟩)
      · exact Or.inr (Or.inr ⟨h1.trans hGbk, hGad.symm.trans h2⟩)
end ACell
end ULHC
