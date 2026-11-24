-- Prove2me | solution 1 for ULHC.Edge.q_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:23:15.104379+00:00
-- url     : https://prove2.me/submissions/f7002fb1-57d9-44f3-8b1f-c50dc4adac7f

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
namespace Edge
theorem _root_.solution (e : Edge) : e.q.1 + e.q.2 = e.p.1 + e.p.2 + 1 := by
  obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [Edge.q] <;> ring
end Edge
end ULHC
