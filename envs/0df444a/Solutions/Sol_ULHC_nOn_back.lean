-- Prove2me | solution 1 for ULHC.nOn_back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:30:44.528826+00:00
-- url     : https://prove2.me/submissions/23338bd2-bcb4-4a3c-a5c2-d7fbbb8fdc97

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_nOn_eq
import Theorems.Thm_ULHC_back_mem_zero
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_back_not_mem
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) : nOn c s n (back c s) = 1 := by
  rw [nOn_eq c s n _ {0}]
  · simp
  · intro m _
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact back_not_mem c s hne h
    · rintro rfl; exact back_mem_zero c s
  · simp; omega
end ULHC
