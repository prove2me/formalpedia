-- Prove2me | solution 1 for ULHC.e1_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:41:14.485351+00:00
-- url     : https://prove2.me/submissions/db5ac187-5ebf-493f-9af3-6caf58eb0b74

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_chain_lat
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_frame_ne
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_inter_unique
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_latB_opp_eq
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_side_nb_next
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side1_down
import Theorems.Thm_ULHC_side2_down
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side_cases
import Theorems.Thm_ULHC_side_lat2
import Theorems.Thm_ULHC_strip_sig
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
include hG hk hcell hpat
namespace ULHC
theorem _root_.solution {τ w : StripSpec} (hl : CR2 V G τ w) (hok : ChainOK τ w)
    (hend : endCell τ = nb (cellJ c s (k + 1)) s) (ht : τ.s = s.opp)
    (hul1 : lat1 (nb (cellJ c s (k + 1)) s) s ∈ G) (hul2 : lat2 (nb (cellJ c s (k + 1)) s) s ∈ G)
    {y : Edge} (hy : y ∈ cellE (cellJ w.c w.s 0)) (hyu : y ∈ cellE (nb (cellJ c s (k + 1)) s))
    (hyl : y = lat1 (nb (cellJ c s (k + 1)) s) τ.s ∨ y = lat2 (nb (cellJ c s (k + 1)) s) τ.s) :
    Touches ⟨c, s, k + 2⟩ w := by
  set e := cellJ c s (k + 1)
  set u := nb e s
  have hc1 := hl.2.2.1
  have hpw := hl.2.2.2.1
  have hne := hl.2.2.2.2.2.2.1
  rw [hend] at hpw hne
  rw [cellJ_zero] at hy
  have hne0 : w.c ≠ u := by have := hne 0 hc1; rwa [cellJ_zero] at this
  rw [ht, (frame_opp u s).1, (frame_opp u s).2.1] at hyl
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ G := a1.2 (by omega)
  have l2 : lat2 e s ∈ G := a2.2 (by omega)
  have hfe : front e s ∉ G := fun h => by have := (af.1 h).1 (by omega); omega
  have hce := hcell (k + 1) le_rfl
  have hlu : lat1 (endCell τ) τ.s ∈ G ∧ lat2 (endCell τ) τ.s ∈ G := by
    rw [hend, ht, (frame_opp u s).1, (frame_opp u s).2.1]; exact ⟨hul1, hul2⟩
  have hyu' : y ∈ cellE (endCell τ) := by rw [hend]; exact hyu
  have hcl := chain_lat hl hok hlu hy hyu'
  have hu_eq : nb e s = cellJ c s (k + 2) := nb_cellJ c s (k + 1)
  rcases hyl with rfl | rfl
  · -- The shared side is `u`'s `lat1`: `w` starts at the cell across it.
    --
    have hw0 : w.c = nb u (latA s) := by
      rcases cell_of_side u (tf := latA s) (by rw [← lat1_eq]; exact hy) with h | h
      · exact absurd h hne0
      · exact h
    have hy2 : lat1 u s = lat2 w.c s := by
      rw [hw0, lat2_eq, latB_eq_opp, show sideEdge (nb u (latA s)) (latA s).opp = back (nb u (latA s)) (latA s)
        from rfl, back_nb, lat1_eq]; rfl
    have hbo : back w.c s = outer1 e s := by rw [hw0, outer1_side_nb_next]; rfl
    have hoff : outer1 e s ∉ G := by
      have hd := hG.2 _ (corners4 hce s).2.2.1
      rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_mem hul1] at hd
      intro ho; rw [ind_of_mem ho] at hd; omega
    have hbu : back w.c s ∉ cellE u := by
      intro h
      have := inter_unique hne0 (by rw [cellE_frame w.c s]; simp) h hy hyu
      rw [hy2] at this
      exact (frame_ne w.c s).2.1 this
    have hbF : back w.c s ∉ flip G u := by rw [mem_flip_off hbu, hbo]; exact hoff
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := frame_ne w.c s
    rcases side_cases s w.s with h | h | h | h
    · exfalso; have := hpw.1; rw [h] at this; exact hbF this
    · have hf0 := hpw.2.2 0 hc1
      rw [cellJ_zero, h, (frame_opp w.c s).2.2.2] at hf0
      have h1n : 1 < w.n := by
        by_contra hn; exact hbF (hf0.2 ⟨fun h' => by omega, fun h' => absurd h' hn⟩)
      refine ⟨1, h1n, k + 1, show k + 1 < k + 2 by omega, lat1 e s, ?_, by rw [cellE_frame e s]; simp⟩
      have hc1' : cellJ w.c w.s 1 = nb e (latA s) := by
        rw [← nb_cellJ, cellJ_zero, h, hw0, show u = cellJ c s (k + 2) from hu_eq, side1_down]
      rw [hc1', ← side_lat2, cellE_frame _ s]; simp
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latA w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n2 hc.symm
      · exact n4 hc.symm
      · exact n4 hc.symm
      · exact n2 hc.symm
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latB w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n2 hc.symm
      · exact n4 hc.symm
      · exact n4 hc.symm
      · exact n2 hc.symm
  · have hw0 : w.c = nb u (latB s) := by
      rcases cell_of_side u (tf := latB s) (by rw [← lat2_eq]; exact hy) with h | h
      · exact absurd h hne0
      · exact h
    have hy2 : lat2 u s = lat1 w.c s := by
      rw [hw0, lat1_eq, ← latB_opp_eq, show sideEdge (nb u (latB s)) (latB s).opp = back (nb u (latB s)) (latB s)
        from rfl, back_nb, lat2_eq]; rfl
    have hbo : back w.c s = outer2 e s := by rw [hw0, outer2_side_nb_next]; rfl
    have hoff : outer2 e s ∉ G := by
      have hd := hG.2 _ (corners4 hce s).2.2.2
      rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_mem hul2] at hd
      intro ho; rw [ind_of_mem ho] at hd; omega
    have hbu : back w.c s ∉ cellE u := by
      intro h
      have := inter_unique hne0 (by rw [cellE_frame w.c s]; simp) h hy hyu
      rw [hy2] at this
      exact (frame_ne w.c s).1 this
    have hbF : back w.c s ∉ flip G u := by rw [mem_flip_off hbu, hbo]; exact hoff
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := frame_ne w.c s
    rcases side_cases s w.s with h | h | h | h
    · exfalso; have := hpw.1; rw [h] at this; exact hbF this
    · have hf0 := hpw.2.2 0 hc1
      rw [cellJ_zero, h, (frame_opp w.c s).2.2.2] at hf0
      have h1n : 1 < w.n := by
        by_contra hn; exact hbF (hf0.2 ⟨fun h' => by omega, fun h' => absurd h' hn⟩)
      refine ⟨1, h1n, k + 1, show k + 1 < k + 2 by omega, lat2 e s, ?_, by rw [cellE_frame e s]; simp⟩
      have hc1' : cellJ w.c w.s 1 = nb e (latB s) := by
        rw [← nb_cellJ, cellJ_zero, h, hw0, show u = cellJ c s (k + 2) from hu_eq, side2_down]
      rw [hc1', ← side2_lat1, cellE_frame _ s]; simp
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latA w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n1 hc.symm
      · exact n3 hc.symm
      · exact n3 hc.symm
      · exact n1 hc.symm
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latB w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n1 hc.symm
      · exact n3 hc.symm
      · exact n3 hc.symm
      · exact n1 hc.symm
end ULHC
