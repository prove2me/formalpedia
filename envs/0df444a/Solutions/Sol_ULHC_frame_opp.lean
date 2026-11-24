-- Prove2me | solution 1 for ULHC.frame_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:21.677885+00:00
-- url     : https://prove2.me/submissions/ae400230-1c76-4aef-a5c3-9ac4a7bc4a5b

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latA_opp
import Theorems.Thm_ULHC_latB_opp
import Theorems.Thm_ULHC_opp_opp


set_option autoImplicit true
open ULHC
open Finset
variable (d : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : lat1 d s.opp = lat1 d s ∧ lat2 d s.opp = lat2 d s ∧
    back d s.opp = front d s ∧ front d s.opp = back d s := by
  refine ⟨by rw [lat1_eq, lat1_eq, latA_opp], by rw [lat2_eq, lat2_eq, latB_opp], ?_, rfl⟩
  show sideEdge d s.opp.opp = sideEdge d s
  rw [opp_opp]
end ULHC
