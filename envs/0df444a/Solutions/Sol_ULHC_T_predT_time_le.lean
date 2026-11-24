-- Prove2me | solution 1 for ULHC.T.predT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:39.895031+00:00
-- url     : https://prove2.me/submissions/5a51005d-34a2-4686-be59-24e42905e6f4

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TwoFactor
import Theorems.Thm_ULHC_T_bwdT_time
import Theorems.Thm_ULHC_T_lfindT_time_le


set_option autoImplicit true
open ULHC ULHC.T
open Finset TF
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) :
    (predT V F L v).time ≤ predCost := by
  have := lfindT_time_le (bwdT V F L v) (inc4 v) 8 (fun e _ => (bwdT_time V F L v e).le)
  have hl : (inc4 v).length = 4 := rfl
  unfold predT predCost
  omega
end ULHC.T
