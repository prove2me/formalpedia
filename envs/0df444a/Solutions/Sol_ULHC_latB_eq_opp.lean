-- Prove2me | solution 1 for ULHC.latB_eq_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:59.345127+00:00
-- url     : https://prove2.me/submissions/14de8cec-887f-48bb-a4e1-e5f9c2686533

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57

set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (tf : Side) : latB tf = (latA tf).opp := by cases tf <;> rfl
end ULHC
