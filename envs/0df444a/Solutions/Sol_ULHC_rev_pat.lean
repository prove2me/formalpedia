-- Prove2me | solution 1 for ULHC.rev_pat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:01.468393+00:00
-- url     : https://prove2.me/submissions/79c0dac4-ba79-4f99-892b-6a47b0893aa6

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Theorems.Thm_ULHC_rev_cellJ
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_back_after
import Theorems.Thm_ULHC_back_after_j
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_front_end_after
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat2_after
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution : StripPat (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) := by
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [(frame_opp _ s).2.2.1]; exact front_end_after hk hpat
  · rw [rev_cellJ c s (by omega), (frame_opp _ s).1, (frame_opp _ s).2.1,
      lat1_after hk hpat (by omega), lat2_after hk hpat (by omega)]
    omega
  · rw [rev_cellJ c s (by omega), (frame_opp _ s).2.2.2]
    by_cases hj : i ≤ k
    · rw [back_after_j hk hpat (by omega) (by omega)]; omega
    · rw [show k + 1 - i = 0 by omega, cellJ_zero]
      simp only [back_after hk hpat, false_iff]
      omega
end ULHC
