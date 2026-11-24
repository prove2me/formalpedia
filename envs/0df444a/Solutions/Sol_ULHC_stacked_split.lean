-- Prove2me | solution 1 for ULHC.stacked_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:39.043285+00:00
-- url     : https://prove2.me/submissions/10ce7ae5-ae9e-48fd-9515-1ca24988ca14

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_series_reduce
import Theorems.Thm_ULHC_mem_cellE_frame
import Theorems.Thm_ULHC_stk_lat1_up
import Theorems.Thm_ULHC_stk_lat2_up
import Theorems.Thm_ULHC_stk_lat1_dn
import Theorems.Thm_ULHC_stk_lat2_dn
import Theorems.Thm_ULHC_stk_front_mem
import Theorems.Thm_ULHC_stk_f1_f2
import Theorems.Thm_ULHC_stk_f2_f1
import Theorems.Thm_ULHC_stk_b1_f2
import Theorems.Thm_ULHC_stk_b2_f1
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Deg2_le_two
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mkLat_cellE
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {e : Pt} {s : Side}
    (he : IsCell V e) (hu : IsCell V (nb e s))
    (el1 : lat1 e s ∈ F) (el2 : lat2 e s ∈ F) (eb : back e s ∉ F) (ef : front e s ∉ F)
    (ul1 : lat1 (nb e s) s ∈ F) (ul2 : lat2 (nb e s) s ∈ F) (uf : front (nb e s) s ∉ F)
    {p q : Pt} (hp1 : p ≠ front1 e s) (hp2 : p ≠ front2 e s)
    (hq1 : q ≠ front1 e s) (hq2 : q ≠ front2 e s) :
    Conn (flip F e) p q ↔ Conn (flip F (nb e s)) p q := by
  set u := nb e s with hu_def
  set m1 := front1 e s
  set m2 := front2 e s
  have hb1 : back1 u s = m1 := back1_nb e s
  have hb2 : back2 u s = m2 := back2_nb e s
  have hbk : back u s = front e s := back_nb e s
  have ub : back u s ∉ F := by rw [hbk]; exact ef
  obtain ⟨_, _, vm1, vm2⟩ := isCell_corners he s
  have hFe : Deg2 V (flip F e) := hF.flip (mkLat e s) he (mkLat_cellE e s) el1 el2 eb ef
  have hFu : Deg2 V (flip F u) := hF.flip (mkLat u s) hu (mkLat_cellE u s) ul1 ul2 ub uf
  -- The common reduced edge set.
  --
  set K : Finset Edge :=
    (F \ {lat1 e s, lat2 e s, lat1 u s, lat2 u s}) ∪ {back e s, front u s} with hK_def
  have memK : ∀ g, g ∈ K ↔
      (g ∈ F ∧ ¬ (g = lat1 e s ∨ g = lat2 e s ∨ g = lat1 u s ∨ g = lat2 u s)) ∨
        (g = back e s ∨ g = front u s) := by
    intro g
    simp only [K, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  -- Ends of the edges involved.
  --
  have eL1u : Ends (lat1 u s) m1 (front1 u s) := by
    have := ends_lat1 u s; rwa [hb1] at this
  have eL2u : Ends (lat2 u s) m2 (front2 u s) := by
    have := ends_lat2 u s; rwa [hb2] at this
  have eFe : Ends (front e s) m1 m2 := ends_front e s
  have eFu : Ends (front u s) (front1 u s) (front2 u s) := ends_front u s
  have eL1e : Ends (lat1 e s) (back1 e s) m1 := ends_lat1 e s
  have eL2e : Ends (lat2 e s) (back2 e s) m2 := ends_lat2 e s
  have eBe : Ends (back e s) (back1 e s) (back2 e s) := ends_back e s
  have i1 : ∀ {g : Edge} {x y : Pt}, Ends g x y → (g.p = x ∨ g.q = x) :=
    fun h => (h.inc_iff _).2 (Or.inl rfl)
  have i2 : ∀ {g : Edge} {x y : Pt}, Ends g x y → (g.p = y ∨ g.q = y) :=
    fun h => (h.inc_iff _).2 (Or.inr rfl)
  have ceE := mem_cellE_frame e s
  have ceU := mem_cellE_frame u s
  have l1e_e : lat1 e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have l2e_e : lat2 e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have l1u_u : lat1 u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have l2u_u : lat2 u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have fe_e : front e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inl rfl))
  have be_e : back e s ∈ cellE e := (ceE _).2 (Or.inl rfl)
  have fu_u : front u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inl rfl))
  have fe_u : front e s ∈ cellE u := stk_front_mem e s
  -- Reduce `flip F e` to `K`: the path `front1 u – m1 – m2 – front2 u`, shortcut `front u`.
  --
  have redE : Conn (flip F e) p q ↔ Conn K p q := by
    refine series_reduce eL1u.swap eFe eL2u eFu ?_ ?_ ?_ ?_ (stk_f1_f2 e s) (stk_f2_f1 e s)
      (hFe.le_two _) (hFe.le_two _) ?_ ?_ hp1 hp2 hq1 hq2
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat1_up e s, fun _ => ul1⟩
    · exact mem_flip_iff.2 ⟨fun h => absurd h ef, fun h => absurd fe_e h⟩
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat2_up e s, fun _ => ul2⟩
    · exact (memK _).2 (Or.inr (Or.inr rfl))
    · intro g hg n1 n2
      rw [mem_flip_iff] at hg
      by_cases hgF : g ∈ F
      · have hgc := hg.1 hgF
        refine (memK g).2 (Or.inl ⟨hgF, ?_⟩)
        rintro (rfl | rfl | rfl | rfl)
        · exact hgc l1e_e
        · exact hgc l2e_e
        · exact n1 (i1 eL1u)
        · exact n2 (i1 eL2u)
      · have hgc : g ∈ cellE e := by by_contra h; exact hgF (hg.2 h)
        rcases (ceE _).1 hgc with rfl | rfl | rfl | rfl
        · exact (memK _).2 (Or.inr (Or.inl rfl))
        · exact absurd (i1 eFe) n1
        · exact absurd el1 hgF
        · exact absurd el2 hgF
    · intro g hg
      rcases (memK g).1 hg with ⟨hgF, hn⟩ | rfl | rfl
      · left
        refine mem_flip_iff.2 ⟨fun _ hgc => ?_, fun _ => hgF⟩
        rcases (ceE _).1 hgc with rfl | rfl | rfl | rfl
        · exact eb hgF
        · exact ef hgF
        · exact hn (Or.inl rfl)
        · exact hn (Or.inr (Or.inl rfl))
      · left
        exact mem_flip_iff.2 ⟨fun h => absurd h eb, fun h => absurd be_e h⟩
      · right; rfl
  -- Reduce `flip F u` to `K`: the path `back1 e – m1 – m2 – back2 e`, shortcut `back e`.
  --
  have redU : Conn (flip F u) p q ↔ Conn K p q := by
    refine series_reduce eL1e eFe eL2e.swap eBe ?_ ?_ ?_ ?_ (stk_b1_f2 e s) (stk_b2_f1 e s)
      (hFu.le_two _) (hFu.le_two _) ?_ ?_ hp1 hp2 hq1 hq2
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat1_dn e s, fun _ => el1⟩
    · exact mem_flip_iff.2 ⟨fun h => absurd h ef, fun h => absurd fe_u h⟩
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat2_dn e s, fun _ => el2⟩
    · exact (memK _).2 (Or.inr (Or.inl rfl))
    · intro g hg n1 n2
      rw [mem_flip_iff] at hg
      by_cases hgF : g ∈ F
      · have hgc := hg.1 hgF
        refine (memK g).2 (Or.inl ⟨hgF, ?_⟩)
        rintro (rfl | rfl | rfl | rfl)
        · exact n1 (i2 eL1e)
        · exact n2 (i2 eL2e)
        · exact hgc l1u_u
        · exact hgc l2u_u
      · have hgc : g ∈ cellE u := by by_contra h; exact hgF (hg.2 h)
        rcases (ceU _).1 hgc with rfl | rfl | rfl | rfl
        · rw [hbk] at n1; exact absurd (i1 eFe) n1
        · exact (memK _).2 (Or.inr (Or.inr rfl))
        · exact absurd ul1 hgF
        · exact absurd ul2 hgF
    · intro g hg
      rcases (memK g).1 hg with ⟨hgF, hn⟩ | rfl | rfl
      · left
        refine mem_flip_iff.2 ⟨fun _ hgc => ?_, fun _ => hgF⟩
        rcases (ceU _).1 hgc with rfl | rfl | rfl | rfl
        · exact ub hgF
        · exact uf hgF
        · exact hn (Or.inr (Or.inr (Or.inl rfl)))
        · exact hn (Or.inr (Or.inr (Or.inr rfl)))
      · right; rfl
      · left
        exact mem_flip_iff.2 ⟨fun h => absurd h uf, fun h => absurd fu_u h⟩
  rw [redE, redU]
end ULHC
