-- Prove2me | solution 1 for ULHC.Adj.unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:13.217124+00:00
-- url     : https://prove2.me/submissions/f51b5d86-e85f-4084-965a-6f07394d0da0

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
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
namespace ULHC
namespace Adj
theorem _root_.solution {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Unit a b := by
  obtain ⟨⟨d, p⟩, _, h⟩ := h
  unfold Unit
  cases d <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> simp [Edge.q]
end Adj
end ULHC
