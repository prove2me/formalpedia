-- Prove2me | solution 1 for ULHC.Edge.ext_pq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:23:19.159147+00:00
-- url     : https://prove2.me/submissions/66c35101-733c-4be7-b4a7-be4a6b85d3f3

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
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
theorem _root_.solution {e e' : Edge} (h1 : e.p = e'.p) (h2 : e.q = e'.q) : e = e' := by
  obtain ⟨d, p⟩ := e
  obtain ⟨d', p'⟩ := e'
  simp only at h1
  subst h1
  cases d <;> cases d' <;> simp_all [Edge.q]
end Edge
end ULHC
