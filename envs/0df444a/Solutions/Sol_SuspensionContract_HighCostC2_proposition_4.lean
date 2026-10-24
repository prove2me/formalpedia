-- Prove2me | solution 1 for SuspensionContract.HighCostC2.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:50:49.610506+00:00
-- url     : https://prove2.me/submissions/4cbe5e49-9061-408b-aef0-f7a58fd260db

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting
import Theorems.Thm_SuspensionContract_HighCostC2_proposition_4_i
import Theorems.Thm_SuspensionContract_HighCostC2_proposition_4_ii

open SuspensionContract.HighCostC2

theorem solution (P : Params) (hP : P.Standing) (h2 : P.Condition2) :
    (P.Vbar - P.vlow < P.K → P.OptCond P.VI31 (fun _ => P.vlow)) ∧
      (P.Kbar2 < P.K → P.K ≤ P.Vbar - P.vlow → P.OptCond P.VI31 P.V032) :=
  ⟨fun hK => proposition_4_i P hP h2 hK, fun hK1 hK2 => proposition_4_ii P hP h2 hK1 hK2⟩
