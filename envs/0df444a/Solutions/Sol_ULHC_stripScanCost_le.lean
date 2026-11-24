-- Prove2me | solution 1 for ULHC.stripScanCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:33.958521+00:00
-- url     : https://prove2.me/submissions/3d95788a-9022-4f60-aeba-23cdb82026c3

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, stripScanCost V F c s k j ≤ 20 * (k + 1) := by
  intro k
  induction k with
  | zero => intro j; simp [stripScanCost]
  | succ k ih =>
    intro j
    simp only [stripScanCost]
    have := ih (j + 1)
    split_ifs <;> omega
end ULHC
