-- Prove2me | solution 1 for P2M_ULHC_body_not_alt__d3691623e2ed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:39:32.204393+00:00
-- url     : https://prove2.me/submissions/1ce2f559-20fb-437a-b9fb-5d607bd5f48a

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (hk : k % 2 = 0)
    (hpat : StripPat F c s (k + 2)) {j : ℕ} (hj : j ≤ k) {tw : Side}
    (l1 : lat1 (cellJ c s j) tw ∈ F) (l2 : lat2 (cellJ c s j) tw ∈ F)
    (bw : back (cellJ c s j) tw ∉ F) (fw : front (cellJ c s j) tw ∉ F) : False := by
  obtain ⟨_, _, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have := (alt_frame s l1 l2 bw fw).1
  rw [ab, af] at this; omega
end ULHC
