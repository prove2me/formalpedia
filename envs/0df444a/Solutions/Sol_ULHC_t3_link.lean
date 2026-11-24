-- Prove2me | solution 1 for ULHC.t3_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:25:05.583377+00:00
-- url     : https://prove2.me/submissions/a52d949d-9677-4b59-a518-be312358c02d

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_alt_frame2
import Theorems.Thm_ULHC_front1_nb_opp
import Theorems.Thm_ULHC_front2_nb_opp
import Theorems.Thm_ULHC_behind_lat1_not_mem
import Theorems.Thm_ULHC_behind_lat2_not_mem
import Theorems.Thm_ULHC_chainOK_besideA
import Theorems.Thm_ULHC_chainOK_besideB
import Theorems.Thm_ULHC_chainOK_far
import Theorems.Thm_ULHC_back_side0_not_mem
import Theorems.Thm_ULHC_back_side0_not_mem2
import Theorems.Thm_ULHC_end_side_link1
import Theorems.Thm_ULHC_end_side_link2
import Theorems.Thm_ULHC_far_link
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_allConn_of_frame
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_back_after
import Theorems.Thm_ULHC_back_after_j
import Theorems.Thm_ULHC_back_down
import Theorems.Thm_ULHC_back_down2
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_cellJ_down
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_front_end_after
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_mem_flipCol_out
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_notTypeIII_of_allConn
import Theorems.Thm_ULHC_outer1_not_mem
import Theorems.Thm_ULHC_outer2_not_mem
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side1_facts
import Theorems.Thm_ULHC_side2_facts
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_lat2
import Theorems.Thm_ULHC_start_notTypeIII
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_touch_cases
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution (h3 : ¬ NoTypeIII V (flipCol F c s (k + 2))) :
    ∃ τ : StripSpec, τ.n = 1 ∧ CR2 V F ⟨c, s, k + 2⟩ τ ∧ ChainOK ⟨c, s, k + 2⟩ τ := by
  set F' := flipCol F c s (k + 2)
  unfold NoTypeIII at h3
  push Not at h3
  obtain ⟨d, hd, tf, hb, hf, hl1, hl2, hn⟩ := h3
  by_cases hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)
  · refine ⟨_, rfl, far_link hF hT hk hcell hpat hsep hd hb hf hl1 hl2 hn hfar,
      chainOK_far fun j hj x hx hxe => ?_⟩
    simp only at hj
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact hfar (k + 1) (by omega) x hx hxe
  push Not at hfar
  obtain ⟨j, hj, x, hx, hxj⟩ := hfar
  have alt := alt_frame2 s hb hf hl1 hl2
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- `d` is not a cell of the strip.
  --
  have body : ∀ j' ≤ k + 1, d ≠ cellJ c s j' := by
    intro j' hj' hdj
    rw [hdj] at alt hn hb hf hl1 hl2
    rcases j' with _ | j'
    · rw [cellJ_zero] at alt hn hb hf hl1 hl2
      exact hn (start_notTypeIII hF hT hk hcell hpat hsep tf hb hf hl1 hl2)
    · by_cases hjk : j' + 1 ≤ k
      · have := alt.1
        rw [back_after_j hk hpat (by omega) (by omega), front_after hk hpat hjk] at this
        omega
      · obtain rfl : j' = k := by omega
        have := alt.1
        rw [back_after_j hk hpat (by omega) le_rfl] at this
        have := this.2 (front_end_after hk hpat); omega
  -- From a dark outer edge at the end cell's front, a link beside the end cell.
  --
  have ldeg : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F → outer1 (cellJ c s (k + 1)) s ∈ F := by
    intro hu
    have l1 := (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
    have hfe : front (cellJ c s (k + 1)) s ∉ F := fun h => by
      have := ((strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.2.1 h).1 (by omega); omega
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hu] at hd
    by_contra ho; rw [ind_of_not_mem ho] at hd; omega
  rcases touch_cases s hx hxj with hq | hq | hq | hq | hq
  · exact absurd hq (body j (by omega))
  · by_cases hjk : j ≤ k
    · exact absurd (by rw [hq, nb_cellJ]) (body (j + 1) (by omega))
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hbu : back (nb (cellJ c s (k + 1)) s) s ∈ F' := by
        rw [back_nb]; exact front_end_after hk hpat
      have hlu : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F' := alt.2.2.1 hbu
      have hlu' : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F := by
        rw [nb_cellJ] at hlu ⊢
        rwa [mem_flipCol_out (fun i hi => lat1_not_mem c s (by omega))] at hlu
      exact ⟨_, rfl, end_side_link1 hF hT hk hcell hpat hsep (ldeg hlu'), chainOK_besideA c s k⟩
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      rw [hq] at alt hn hb hf hl1 hl2
      have d1 := back_down hF hT hpat (by omega) hc0 hsep
      have d2 := back_down2 hF hT hpat (by omega) hc0 hsep
      have d1' : lat1 (nb c s.opp) s ∈ F' := by
        rw [show cellJ c s 0 = c from cellJ_zero c s] at *
        rw [mem_flipCol_out (fun i _ => behind_lat1_not_mem c s i)]; exact d1
      have d2' : lat2 (nb c s.opp) s ∈ F' := by
        rw [mem_flipCol_out (fun i _ => behind_lat2_not_mem c s i)]; exact d2
      have hbB : back (nb c s.opp) s ∉ F' := fun h => (alt.2.2.1 h) d1'
      -- `c` is alternating after the flip and not Type III, so its corners are joined.
      --
      have l1c : lat1 c s ∈ F' := by
        have := (lat1_after hk hpat (j := 0) (by omega)).2 rfl; rwa [cellJ_zero] at this
      have l2c : lat2 c s ∈ F' := by
        have := (lat2_after hk hpat (j := 0) (by omega)).2 rfl; rwa [cellJ_zero] at this
      have fc : front c s ∉ F' := fun h => by
        have := (front_after hk hpat (j := 0) (by omega)).1 (by rw [cellJ_zero]; exact h); omega
      have hac : Alt F' c := alt_of_lats l1c l2c (back_after hk hpat) fc
      have hcc : AllConn F' c := alt_corners_conn' (start_notTypeIII hF hT hk hcell hpat hsep) hac
      have hbb := (frame_of_allConn hcc s).1
      have e1 := ends_lat1 (nb c s.opp) s
      have e2 := ends_lat2 (nb c s.opp) s
      rw [front1_nb_opp] at e1; rw [front2_nb_opp] at e2
      have h2 : Conn F' (back1 (nb c s.opp) s) (back1 c s) := e1.conn d1'
      have h3 : Conn F' (back1 (nb c s.opp) s) (back2 c s) := h2.trans hbb
      have h1 : Conn F' (back1 (nb c s.opp) s) (back2 (nb c s.opp) s) := h3.trans (e2.conn d2').symm
      have hall : AllConn F' (nb c s.opp) := allConn_of_frame s h1
        (by rw [front1_nb_opp]; exact h2) (by rw [front2_nb_opp]; exact h3)
      exact hn (notTypeIII_of_allConn (V := V) hall tf hb hf hl1 hl2)
    · exact absurd (by rw [hq, cellJ_down]) (body j (by omega))
  · by_cases hjk : j ≤ k
    · exfalso
      obtain ⟨_, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hjk
      rw [hq] at alt
      have fb' : back (nb (cellJ c s j) (latA s)) s ∈ F' ↔ j % 2 = 1 := by
        rcases j with _ | j
        · rw [mem_flipCol_out (fun i _ => by rw [cellJ_zero]; exact back_side0_not_mem c s i)]
          exact fb
        · rw [← nb_cellJ, side_back_next, mem_flipCol_out (fun i _ => outer1_not_mem c s j i)]
          rw [← nb_cellJ, side_back_next] at fb; exact fb
      have ff' : front (nb (cellJ c s j) (latA s)) s ∈ F' ↔ j % 2 = 0 := by
        rw [side_front, mem_flipCol_out (fun i _ => outer1_not_mem c s j i), ← side_front]
        exact ff
      have := alt.1; rw [fb', ff'] at this; omega
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hn' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F' := by
        rw [side_lat2, lat1_after hk hpat le_rfl]; omega
      have hl1' : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F' := fun h => hn' (alt.2.1.1 h)
      have hbk := (alt.2.2).2 hl1'
      have hfr := alt.1.1 hbk
      rw [side_front, mem_flipCol_out (fun i _ => outer1_not_mem c s (k + 1) i)] at hfr
      exact ⟨_, rfl, end_side_link1 hF hT hk hcell hpat hsep hfr, chainOK_besideA c s k⟩
  · by_cases hjk : j ≤ k
    · exfalso
      obtain ⟨_, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hjk
      rw [hq] at alt
      have fb' : back (nb (cellJ c s j) (latB s)) s ∈ F' ↔ j % 2 = 1 := by
        rcases j with _ | j
        · rw [mem_flipCol_out (fun i _ => by rw [cellJ_zero]; exact back_side0_not_mem2 c s i)]
          exact fb
        · have hbo : back (nb (cellJ c s (j + 1)) (latB s)) s = outer2 (cellJ c s j) s := by
            rw [outer2_side_nb_next, nb_cellJ]; rfl
          rw [hbo, mem_flipCol_out (fun i _ => outer2_not_mem c s j i)]
          rw [hbo] at fb; exact fb
      have ff' : front (nb (cellJ c s j) (latB s)) s ∈ F' ↔ j % 2 = 0 := by
        rw [side2_front, mem_flipCol_out (fun i _ => outer2_not_mem c s j i), ← side2_front]
        exact ff
      have := alt.1; rw [fb', ff'] at this; omega
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hn' : lat1 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F' := by
        rw [side2_lat1, lat2_after hk hpat le_rfl]; omega
      have hbk := (alt.2.2).2 hn'
      have hfr := alt.1.1 hbk
      rw [side2_front, mem_flipCol_out (fun i _ => outer2_not_mem c s (k + 1) i)] at hfr
      exact ⟨_, rfl, end_side_link2 hF hT hk hcell hpat hsep hfr, chainOK_besideB c s k⟩
end ULHC
