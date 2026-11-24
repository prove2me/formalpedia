-- Prove2me | solution 1 for ULHC.not_mid_back2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:21:44.926902+00:00
-- url     : https://prove2.me/submissions/803b75f2-be19-4d48-8a00-543a179de1c1

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
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
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) : ¬ IsMid c s k (back2 c s) := by
  rintro ⟨j, hj, _, h | h⟩ <;> obtain ⟨x, y⟩ := c <;> cases s <;>
    simp [back2, front1, front2, cellJ] at h <;> omega
end ULHC
