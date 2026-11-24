-- Prove2me | solution 1 for ULHC.rev_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:15:01.105794+00:00
-- url     : https://prove2.me/submissions/d64212a8-8d77-4c6c-a3bd-9472f29a74f1

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Theorems.Thm_ULHC_rev_cellJ
import Theorems.Thm_ULHC_rev_pat
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_conn_lat1_opp
import Theorems.Thm_ULHC_end_corners


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'
omit hs x0 hconn hT'
namespace ULHC
theorem _root_.solution :
    ValidStrip V (flipCol F c s (k + 2)) ⟨cellJ c s (k + 1), s.opp, k + 2⟩ := by
  refine ⟨by show 1 ≤ k + 2; omega, rev_pat hk hpat, fun i hi => ?_, ?_⟩
  · change i < k + 2 at hi
    show IsCell V (cellJ (cellJ c s (k + 1)) s.opp i)
    rw [rev_cellJ c s (by omega)]; exact hcell _ (by omega)
  · exact conn_lat1_opp (end_corners hF hT hk hcell hpat hsep).2.2
end ULHC
