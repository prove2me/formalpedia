-- Prove2me | solution 1 for ULHC.along_not_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:17.638798+00:00
-- url     : https://prove2.me/submissions/189fe92b-3e18-46e8-9eda-19d640babdda

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 3)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 3)) s) := by
  obtain ⟨p, q⟩ := c
  constructor <;> rintro ⟨j, hj, hjk, h⟩ <;> cases s <;>
    simp [back1, front1, front2, cellJ] at h <;> omega
end ULHC
