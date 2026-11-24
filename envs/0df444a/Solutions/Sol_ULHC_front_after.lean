-- Prove2me | solution 1 for ULHC.front_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:37:32.773799+00:00
-- url     : https://prove2.me/submissions/b2b5b3ed-6acd-4c79-93bd-fe2334a9887c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_nOn_front_mid
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : j ≤ k) :
    front (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 1 := by
  rw [mem_after, nOn_front_mid c s (by omega), hpat.2.2 j (by omega)]
  have : j + 1 < k + 2 := by omega
  simp [this]
end ULHC
