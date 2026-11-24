-- Prove2me | solution 1 for ULHC.body_not_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:47.952564+00:00
-- url     : https://prove2.me/submissions/82652607-6e1d-43ec-b69f-b8a1aa5e1199

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs x0 hconn hF hT hcell hsep hT' hz
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) {tw : Side} (l1 : lat1 (cellJ c s j) tw ∈ F)
    (l2 : lat2 (cellJ c s j) tw ∈ F) (bw : back (cellJ c s j) tw ∉ F)
    (fw : front (cellJ c s j) tw ∉ F) : False := by
  obtain ⟨_, _, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have := (alt_frame s l1 l2 bw fw).1
  rw [ab, af] at this; omega
end ULHC
