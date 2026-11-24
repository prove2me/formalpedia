-- Prove2me | solution 1 for ULHC.lat1_beyond_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:45.975286+00:00
-- url     : https://prove2.me/submissions/0781c62b-c0d0-4cbc-aa49-59a87ad8ee3c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_not_mem


set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (n m : ℕ) (hm : m < n) :
    lat1 (cellJ c s n) s ∉ cellE (cellJ c s m) := lat1_not_mem c s (by omega)
end ULHC
