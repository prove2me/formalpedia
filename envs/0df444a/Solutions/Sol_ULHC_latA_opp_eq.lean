-- Prove2me | solution 1 for ULHC.latA_opp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:28.824798+00:00
-- url     : https://prove2.me/submissions/6f759f55-e8d2-4a7a-9a47-a5156a5b1994

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_latB_eq_opp


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (s : Side) : (latA s).opp = latB s := by rw [latB_eq_opp]
end ULHC
