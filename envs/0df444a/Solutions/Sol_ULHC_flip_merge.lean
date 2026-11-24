-- Prove2me | solution 1 for ULHC.flip_merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:26.339003+00:00
-- url     : https://prove2.me/submissions/d0729923-7106-41ec-a70f-749137a36df5

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_flip_step1
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_of_edge
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_conn_erase_of_even
import Theorems.Thm_ULHC_conn_insert
import Theorems.Thm_ULHC_conn_insert_of_conn
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_ncomp_congr
import Theorems.Thm_ULHC_ncomp_insert_merge
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
theorem _root_.solution (hn : ¬ Conn F (x, y) (x, y + 1)) :
    ncomp V (flip F (x, y)) + 1 = ncomp V F := by
  obtain ⟨hab, e1⟩ := flip_step1 hV hb h2
  set G1 := F.erase (bot (x, y)) with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have htG1 : top (x, y) ∈ G1 := Finset.mem_erase.2 ⟨by simp [top, bot], ht⟩
  -- Remove the top edge (not a bridge: `d`'s class avoids `a` and `b`).
  have hdk : Conn (G1.erase (top (x, y))) (top (x, y)).p (top (x, y)).q := by
    apply conn_erase_of_even (hV.mono hG1F) htG1
    intro z _ hz
    have hzF : Conn F (x, y + 1) z := hz.mono hG1F
    have hza : ¬ (bot (x, y)).p = z ∧ ¬ (bot (x, y)).q = z := by
      constructor
      · intro h; apply hn; rw [show (bot (x, y)).p = (x, y) from rfl] at h; subst h
        exact hzF.symm
      · intro h; apply hn; rw [show (bot (x, y)).q = (x + 1, y) from rfl] at h; subst h
        exact (Conn.of_edge hb).trans hzF.symm
    have := deg_erase hb z
    rw [if_neg (by tauto), ← hG1, add_zero] at this
    rw [this, h2 z (Or.inr hzF)]; exact even_two
  set G := G1.erase (top (x, y)) with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have e2 : ncomp V G = ncomp V G1 := by
    have := Finset.insert_erase htG1
    conv_rhs => rw [← this]
    apply ncomp_congr
    intro u _ v _
    exact (conn_insert_of_conn hdk u v).symm
  -- `a`, `b` stay joined in `G`.
  have habG : Conn G (x, y) (x + 1, y) := by
    have : Conn (insert (top (x, y)) G) (x, y) (x + 1, y) := by
      rw [Finset.insert_erase htG1]; exact hab
    rcases conn_insert.1 this with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd (h1.mono hGF) hn
    · exact absurd ((h1.mono hGF).trans (Conn.of_edge ht).symm) hn
  -- Insert the left side (merge) and the right side (inside a class).
  have hlv : (lft (x, y)).p ∈ V ∧ (lft (x, y)).q ∈ V := ⟨hc.1, hc.2.2.1⟩
  have em : ncomp V (insert (lft (x, y)) G) + 1 = ncomp V G :=
    ncomp_insert_merge hlv.1 hlv.2 (fun h => hn (h.mono hGF))
  have hbk : Conn (insert (lft (x, y)) G) (rgt (x, y)).p (rgt (x, y)).q := by
    have s : G ⊆ insert (lft (x, y)) G := Finset.subset_insert _ _
    have hl' : Conn (insert (lft (x, y)) G) (x, y) (x, y + 1) :=
      Conn.of_edge (Finset.mem_insert_self _ _)
    exact ((habG.mono s).symm.trans hl').trans (hdk.mono s)
  have er : ncomp V (insert (rgt (x, y)) (insert (lft (x, y)) G)) =
      ncomp V (insert (lft (x, y)) G) := by
    apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn hbk u v
  rw [flip_eq hb ht hl hr, er]
  omega
end ULHC
