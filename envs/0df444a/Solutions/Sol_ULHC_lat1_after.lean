-- Prove2me | solution 1 for ULHC.lat1_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:44:06.199827+00:00
-- url     : https://prove2.me/submissions/01fa6d1d-57de-4297-a162-468fc8c8e198

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_nOn_lat1


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k + 1) :
    lat1 (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  rw [mem_after, nOn_lat1 c s (by omega), (hpat.2.1 j (by omega)).1]; omega
end ULHC
