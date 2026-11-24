-- Prove2me | solution 1 for ULHC.start_L0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:15:29.286555+00:00
-- url     : https://prove2.me/submissions/81fafcad-2571-4738-9510-90d78408c75e

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
import Theorems.Thm_ULHC_back_outer_light
import Theorems.Thm_ULHC_behind_up
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_start
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_front_ends


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
theorem _root_.solution {m : ℕ} (hzs : SigFrom F (nb c (latA s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latA s)) s.opp 1)) (hx : lat1 (nb c (latA s)) s ∈ F) :
    False := by
  set d := nb c (latA s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have ho := outer1_start hF hpat (by omega) hc0
  have hbo := back_outer_light hF hT hpat (by omega) hc0 hsep
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
  have f1 : front1 w s = back1 d s := by rw [← hwd, back1_nb]
  have f2 : front2 w s = back1 c s := by
    have h2 : front2 w s = back2 d s := by rw [← hwd, back2_nb]
    rw [h2]; exact side_back2 c s
  have hfw : front w s ∉ F := by
    have := back_nb w s; rw [hwd] at this; rw [← this]; exact hbo
  have hQ : Conn F (front1 w s) (front1 c s) := by
    rw [f1]; exact ((ends_lat1 d s).conn hx).trans ((side_front_ends c s).conn ho)
  have hff : Conn F (front2 w s) (front1 w s) := by
    by_cases hm2 : m = 2
    · have hbw : back w s ∉ F := fun h => by have := (gf.1 h).1 rfl; omega
      have hall := alt_corners_conn hT hc1 (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a3.symm.trans a2
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat2 w s).conn wl2).symm.trans ((ends_back w s).conn hbw).symm).trans
        ((ends_lat1 w s).conn wl1)
  rw [f2] at hff
  exact hsep (hff.trans hQ)
end ULHC
