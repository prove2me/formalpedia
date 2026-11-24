-- Prove2me | solution 1 for ULHC.lat2_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:43:33.299664+00:00
-- url     : https://prove2.me/submissions/d628d006-d010-4b6f-8033-d474dbdc3758

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_nOn_lat2


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k + 1) :
    lat2 (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  rw [mem_after, nOn_lat2 c s (by omega), (hpat.2.1 j (by omega)).2]; omega
end ULHC
