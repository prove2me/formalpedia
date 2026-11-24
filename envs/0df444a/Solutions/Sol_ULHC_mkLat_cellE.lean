-- Prove2me | solution 1 for ULHC.mkLat_cellE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:31.072868+00:00
-- url     : https://prove2.me/submissions/36ee984c-e9e4-4d54-b681-9caa22c4910c

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_cellE_frame
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
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    cellE c = {(mkLat c s).e1, (mkLat c s).e2, (mkLat c s).l1, (mkLat c s).l2} := by
  rw [cellE_frame c s]; ext e; simp [mkLat]; tauto
end ULHC
