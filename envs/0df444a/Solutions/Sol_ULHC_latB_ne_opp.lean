-- Prove2me | solution 1 for ULHC.latB_ne_opp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:13.627787+00:00
-- url     : https://prove2.me/submissions/7a9e12d6-38e1-4d96-a0f1-d87283d1b075

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (s : Side) : latB s ≠ s.opp := by cases s <;> simp [latB, Side.opp]
end ULHC
