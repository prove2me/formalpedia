-- Prove2me | solution 1 for ULHC.flip_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:32.282799+00:00
-- url     : https://prove2.me/submissions/dda97334-5143-4ee1-9dec-cbc71b845383

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_closed_conn
import Theorems.Thm_ULHC_class_parity
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_flip_step1
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_of_edge
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_conn_insert_of_conn
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_leaves_le_two
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_ncomp_congr
import Theorems.Thm_ULHC_ncomp_insert_merge
import Theorems.Thm_ULHC_planar_cell
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {x y : ℤ}
  (hV : Inside V F) (hc : IsCell V (x, y))
  (hb : bot (x, y) ∈ F) (ht : top (x, y) ∈ F) (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
  (h2 : ∀ z, (Conn F (x, y) z ∨ Conn F (x, y + 1) z) → deg F z = 2)
include hV hc hb ht hl hr h2
namespace ULHC
theorem _root_.solution (hy : Conn F (x, y) (x, y + 1)) (hle : ∀ z, deg F z ≤ 2) :
    ncomp V (flip F (x, y)) = ncomp V F + 1 := by
  obtain ⟨hab, e1⟩ := flip_step1 hV hb h2
  set a : Pt := (x, y) with ha
  set b : Pt := (x + 1, y) with hbb
  set d : Pt := (x, y + 1) with hd
  set k : Pt := (x + 1, y + 1) with hk
  set G1 := F.erase (bot a) with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have htG1 : top a ∈ G1 := Finset.mem_erase.2 ⟨by simp [top, bot, a], ht⟩
  set G := G1.erase (top a) with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have hVG : Inside V G := hV.mono hGF
  have hbG : bot a ∉ G := fun h => by simp [G, G1] at h
  have hlG : lft a ∉ G := fun h => hl (hGF h)
  -- Degrees in `G`.
  set S : Finset Pt := {a, b, d, k} with hS
  have hFab : Conn F a b := Conn.of_edge hb
  have hFdk : Conn F d k := Conn.of_edge ht
  have degG : ∀ z, Conn F a z → deg G z = if z ∈ S then 1 else 2 := by
    intro z hz
    have hz2 := h2 z (Or.inl hz)
    have f1 := deg_erase hb z
    have f2 := deg_erase htG1 z
    rw [← hG1] at f1
    rw [← hG] at f2
    simp only [bot, top, Edge.q, S, Finset.mem_insert, Finset.mem_singleton, a, b, d, k]
      at f1 f2 ⊢
    obtain ⟨z1, z2⟩ := z
    simp only [Prod.mk.injEq] at f1 f2 ⊢
    split_ifs at f1 f2 ⊢ <;> omega
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    have f1 := deg_erase hb z
    have f2 := deg_erase htG1 z
    rw [← hG1] at f1
    rw [← hG] at f2
    have := hle z
    omega
  -- Class bookkeeping.
  have mem_cls : ∀ u w, w ∈ cls V G u ↔ w ∈ V ∧ Conn G u w := by
    intro u w; simp [cls]
  have aV : a ∈ V := hc.1
  have bV : b ∈ V := hc.2.1
  have dV : d ∈ V := hc.2.2.1
  have kV : k ∈ V := hc.2.2.2
  have cnt : ∀ K : Finset Pt, ((K ∩ S).card : ℕ) =
      (if a ∈ K then 1 else 0) + (if b ∈ K then 1 else 0) + (if d ∈ K then 1 else 0) +
        (if k ∈ K then 1 else 0) := by
    intro K
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [hS, Finset.sum_insert (by simp [a, b, d, k]), Finset.sum_insert (by simp [b, d, k]),
      Finset.sum_insert (by simp [d, k]), Finset.sum_singleton]
    ring
  -- Parity and the leaf bound in `a`'s class and `b`'s class.
  have par : ∀ u, Conn F a u → Even ((cls V G u ∩ S).card) := by
    intro u hu
    apply class_parity hVG u S
    intro z hz
    rw [mem_cls] at hz
    exact degG z (hu.trans (hz.2.mono hGF))
  have leaf : ∀ u, Conn F a u → (cls V G u ∩ S).card ≤ 2 := by
    intro u hu
    have hl2 := leaves_le_two (V := V) _ G rfl hVG hleG u
    refine le_trans (Finset.card_le_card ?_) hl2
    intro z hz
    rw [Finset.mem_inter, mem_cls] at hz
    rw [Finset.mem_filter]
    refine ⟨hz.1.1, hz.1.2, ?_⟩
    rw [degG z (hu.trans (hz.1.2.mono hGF)), if_pos hz.2]
  have sym : ∀ u w, w ∈ cls V G u → u ∈ V → u ∈ cls V G w := by
    intro u w hw hu
    rw [mem_cls] at hw ⊢; exact ⟨hu, hw.2.symm⟩
  have aK : a ∈ cls V G a := mem_cls_self aV
  have bK : b ∈ cls V G b := mem_cls_self bV
  have pa := par a (Conn.refl _ _)
  have la := leaf a (Conn.refl _ _)
  have pb := par b hFab
  rw [cnt] at pa la pb
  rw [if_pos aK] at pa la
  rw [if_pos bK] at pb
  by_cases hbA : b ∈ cls V G a
  · -- Then `d`, `k` are outside `a`'s class, so `F` cannot join `a` to `d`.
    exfalso
    rw [if_pos hbA] at la pa
    have hdA : d ∉ cls V G a := by intro h; rw [if_pos h] at la; split_ifs at la <;> omega
    have hkA : k ∉ cls V G a := by intro h; rw [if_pos h] at la; split_ifs at la; omega
    have hcl : Closed F (cls V G a) := by
      intro u hu w huw
      obtain ⟨f, hf, hfw⟩ := huw
      by_cases hfb : f = bot a
      · subst hfb
        rcases hfw with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
        · rw [← h2']; exact hbA
        · rw [← h1]; exact aK
      by_cases hft : f = top a
      · subst hft
        rcases hfw with ⟨h1, _⟩ | ⟨_, h2'⟩
        · rw [← h1] at hu; exact absurd hu hdA
        · rw [← h2'] at hu; exact absurd hu hkA
      · exact closed_cls hVG a u hu w
          ⟨f, Finset.mem_erase.2 ⟨hft, Finset.mem_erase.2 ⟨hfb, hf⟩⟩, hfw⟩
    exact hdA (closed_conn hcl aK hy)
  rw [if_neg hbA] at la pa
  have hAB : ∀ w, w ∈ cls V G a → w ∉ cls V G b := by
    intro w hwa hwb
    apply hbA
    rw [mem_cls] at hwa hwb ⊢
    exact ⟨bV, hwa.2.trans hwb.2.symm⟩
  have haB : a ∉ cls V G b := fun h => hAB a aK h
  rw [if_neg haB] at pb
  by_cases hkA : k ∈ cls V G a
  · -- Twisted pairing: excluded by the planar lemma.
    exfalso
    have hkB : k ∉ cls V G b := hAB k hkA
    rw [if_neg hkB] at pb
    have hdB : d ∈ cls V G b := by
      by_contra h; rw [if_neg h] at pb; simp at pb
    apply planar_cell G x y hbG hlG
    · exact ((mem_cls _ _).1 hdB).2
    · exact ((mem_cls _ _).1 hkA).2.symm
    · intro h; exact hbA ((mem_cls _ _).2 ⟨bV, h⟩)
  · rw [if_neg hkA] at la pa
    have hdA : d ∈ cls V G a := by
      by_contra h; rw [if_neg h] at pa; simp at pa
    have hdB : d ∉ cls V G b := hAB d hdA
    rw [if_neg hdB] at pb
    have hkB : k ∈ cls V G b := by
      by_contra h; rw [if_neg h] at pb; simp at pb
    have hGad : Conn G a d := ((mem_cls _ _).1 hdA).2
    have hGbk : Conn G b k := ((mem_cls _ _).1 hkB).2
    have hGdk : ¬ Conn G d k := by
      intro h; exact hkA ((mem_cls _ _).2 ⟨kV, hGad.trans h⟩)
    -- Count: `G1 = G + top` merges; adding the two sides changes nothing.
    have em : ncomp V G1 + 1 = ncomp V G := by
      have := ncomp_insert_merge (V := V) (F := G) (e := top a) dV kV hGdk
      rw [Finset.insert_erase htG1] at this
      exact this
    have s1 : G ⊆ insert (lft a) G := Finset.subset_insert _ _
    have el : ncomp V (insert (lft a) G) = ncomp V G := by
      apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn hGad u v
    have er : ncomp V (insert (rgt a) (insert (lft a) G)) = ncomp V (insert (lft a) G) := by
      apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn (hGbk.mono s1) u v
    rw [flip_eq hb ht hl hr, er, el]
    omega
end ULHC
