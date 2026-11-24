-- Prove2me | solution 1 for ULHC.chain_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:40:44.02766+00:00
-- url     : https://prove2.me/submissions/4897abdb-b4e6-4eb6-b4ce-ce2ead2811d5

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
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
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_nb_cellJ


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {S : Finset Edge}
namespace ULHC
theorem _root_.solution (_hS : Deg2 V S) (hT : NoTypeIII V S) {d : Pt} {tf : Side} {m : ℕ}
    (hm : 1 ≤ m) (hsig : SigFrom S d tf m 1) (hcell : 2 ≤ m → IsCell V (cellJ d tf 1))
    (hb : back d tf ∈ S) (hf : front d tf ∈ S ↔ m = 1)
    (hx : lat1 d tf ∈ S ∨ lat2 d tf ∈ S) :
    Conn S (back1 d tf) (front1 d tf) := by
  by_cases h1 : lat1 d tf ∈ S
  · exact (ends_lat1 d tf).conn h1
  have h2 : lat2 d tf ∈ S := hx.resolve_left h1
  have p1 : Conn S (back1 d tf) (front2 d tf) :=
    ((ends_back d tf).conn hb).trans ((ends_lat2 d tf).conn h2)
  suffices hff : Conn S (front2 d tf) (front1 d tf) from p1.trans hff
  by_cases hm1 : m = 1
  · exact ((ends_front d tf).conn (hf.2 hm1)).symm
  have c1 : nb d tf = cellJ d tf 1 := by
    have := nb_cellJ d tf 0; rwa [cellJ_zero] at this
  obtain ⟨g1, g2, _, gf⟩ := hsig 1 le_rfl (by omega)
  have l1 : lat1 (cellJ d tf 1) tf ∈ S := g1.2 rfl
  have l2 : lat2 (cellJ d tf 1) tf ∈ S := g2.2 rfl
  have e1 := ends_lat1 (cellJ d tf 1) tf
  have e2 := ends_lat2 (cellJ d tf 1) tf
  rw [← c1, back1_nb] at e1
  rw [← c1, back2_nb] at e2
  by_cases hm2 : m = 2
  · -- The second cell is alternating and not Type III, so its corners are joined.
    --
    have hc := hcell (by omega)
    have bF : back (cellJ d tf 1) tf ∉ S := by
      rw [← c1, back_nb]; exact fun h => hm1 (hf.1 h)
    have fF : front (cellJ d tf 1) tf ∉ S := fun h => by have := (gf.1 h).1 rfl; omega
    have hall := alt_corners_conn hT hc (alt_of_lats l1 l2 bF fF)
    have hbb := (frame_of_allConn hall tf).1
    rw [← c1, back1_nb, back2_nb] at hbb
    exact hbb.symm
  · have fr : front (cellJ d tf 1) tf ∈ S := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
    rw [← c1] at l1 l2 fr
    exact (((e2.conn l2).trans ((ends_front _ tf).conn fr).symm).trans (e1.conn l1).symm)
end ULHC
