-- Prove2me | solution 1 for ULHC.augLoopCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:29:55.902817+00:00
-- url     : https://prove2.me/submissions/dba7da02-2ae9-4dfd-9709-f108547c29b5

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
import Theorems.Thm_ULHC_augStepCost_le
import Theorems.Thm_ULHC_ACell_split
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
open Finset TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) :
    ∀ n F, augLoopCost V n F ≤ 1 + n * (130 * (V.card + 1) ^ 2 + 1) := by
  intro n
  induction n with
  | zero => intro F; simp [augLoopCost]
  | succ n ih =>
    intro F
    simp only [augLoopCost]
    have h1 := augStepCost_le V F
    split
    · nlinarith
    · rename_i F' _
      have := ih F'
      nlinarith
end ULHC
