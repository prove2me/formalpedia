-- Prove2me | solution 1 for ULHC.ulhc_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:55:08.207144+00:00
-- url     : https://prove2.me/submissions/22354775-079b-4767-a941-f27e5ed8142e

import Definitions.Def_ULHC_PathComplete
import Definitions.Def_ULHC_Timed_Alg
import Definitions.Def_ULHC_Main
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_T_ulhcT_ret
import Theorems.Thm_ULHC_T_ulhcT_time_le
import Theorems.Thm_ULHC_ulhcCost_le
import Theorems.Thm_ULHC_ulhc_correct
attribute [local simp] ULHC.T.ulhcT_ret



set_option autoImplicit true
open ULHC
namespace ULHC
theorem _root_.solution {V : Finset Pt} (hs : Solid V) :
    ((T.ulhcT V).ret = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1) ∧
      (T.ulhcT V).time ≤ 500000000 * (V.card + 1) ^ 12 := by
  refine ⟨?_, (T.ulhcT_time_le V).trans (ulhcCost_le V)⟩
  rw [T.ulhcT_ret]
  exact ulhc_correct hs
end ULHC
