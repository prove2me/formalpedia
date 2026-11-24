-- Prove2me | solution 1 for ULHC.side_lat2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:21.664385+00:00
-- url     : https://prove2.me/submissions/199f6a36-e4c0-4eaa-a5dd-91b33b04d692

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_side_nb
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_lat2_eq


set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution : lat2 (nb c (latA s)) s = lat1 c s := by
  rw [lat2_eq, latB_eq_opp, lat1_side_nb]
end ULHC
