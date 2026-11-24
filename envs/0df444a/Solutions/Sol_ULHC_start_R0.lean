-- Prove2me | solution 1 for ULHC.start_R0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:19:34.408809+00:00
-- url     : https://prove2.me/submissions/2788792a-aa2e-409a-a299-ade45d9a767e

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_back_outer2_light
import Theorems.Thm_ULHC_behind_up
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_front_join
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_front_ends


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution {m : ℕ} (hzs : SigFrom F (nb c (latB s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latB s)) s.opp 1)) (hx : lat2 (nb c (latB s)) s ∈ F) :
    False := by
  set d := nb c (latB s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hbo := back_outer2_light hF hT hpat (by omega) hc0 hsep
  have hfj := front_join hF hT hpat (by omega) hc0
  have ho : outer2 c s ∈ F := by
    obtain ⟨_, hl, hf⟩ := hpat
    have h0 := hl 0 (by omega)
    have h1 := hl 1 (by omega)
    have hf0 := hf 0 (by omega)
    rw [cellJ_zero] at h0 hf0
    have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
    have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
    have hl1 : lat2 (nb c s) s ∈ F := by
      rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.2.2 rfl
    have hd := hF.2 _ (corners4 hc0 s).2.2.2
    rw [deg_front2, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
    by_contra ho; rw [ind_of_not_mem ho] at hd; omega
  have h1 : nb d s.opp = cellJ d s.opp 1 := by
    have := nb_cellJ d s.opp 0; rwa [cellJ_zero] at this
  set w := cellJ d s.opp 1
  have hwd : nb w s = d := by rw [← h1]; exact behind_up d s
  obtain ⟨g1, g2, _, gf⟩ := hzs 1 le_rfl (by omega)
  rw [(frame_opp w s).1] at g1
  rw [(frame_opp w s).2.1] at g2
  rw [(frame_opp w s).2.2.2] at gf
  have wl1 : lat1 w s ∈ F := g1.2 rfl
  have wl2 : lat2 w s ∈ F := g2.2 rfl
  have f1 : front1 w s = back2 c s := by
    have h2 : front1 w s = back1 d s := by rw [← hwd, back1_nb]
    rw [h2]; exact side2_back1 c s
  have f2 : front2 w s = back2 d s := by rw [← hwd, back2_nb]
  have hfw : front w s ∉ F := by
    have := back_nb w s; rw [hwd] at this; rw [← this]; exact hbo
  have hQ : Conn F (front2 w s) (front1 c s) := by
    rw [f2]
    exact (((ends_lat2 d s).conn hx).trans ((side2_front_ends c s).conn ho).symm).trans hfj.symm
  have hff : Conn F (front1 w s) (front2 w s) := by
    by_cases hm2 : m = 2
    · have hbw : back w s ∉ F := fun h => by have := (gf.1 h).1 rfl; omega
      have hall := alt_corners_conn hT hc1 (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a2.symm.trans a3
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat1 w s).conn wl1).symm.trans ((ends_back w s).conn hbw)).trans
        ((ends_lat2 w s).conn wl2)
  rw [f1] at hff
  exact hsep (((ends_back c s).conn hpat.1).trans (hff.trans hQ))
end ULHC
