-- Prove2me | solution 1 for ULHC.latB_opp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:56.221723+00:00
-- url     : https://prove2.me/submissions/c8064a4e-ea07-47dc-9e3b-42135889ec37

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_latB_eq_opp
import Theorems.Thm_ULHC_opp_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (s : Side) : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]
end ULHC
