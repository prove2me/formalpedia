-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:35:05.036568+00:00
-- url     : https://prove2.me/submissions/418f7420-276f-4561-ac5d-16468bec8471

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_weight
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_weight


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (i : StepIndex n)
    (s : (SuffixData S n).family.Syndrome i.succ) :
    (if i.val % 2 = 0 then 2 else 1) *
      HammingWeight (actualStep S (n+2) (LevelTwoHistory.physicalStep i) s).coarse.val ≤
        HammingWeight s.val := by
  by_cases h : i.val % 2 = 0
  · have hp : (LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      change (i.val+2)%2=0
      omega
    rw [if_pos h,actualStep_rx S (n+2) _ hp]
    exact BDL26RXDecoderAdapter.rxStepOutput_weight S (n+2) _ hp s
  · have hp : ¬ (LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      change ¬ (i.val+2)%2=0
      omega
    rw [if_neg h,actualStep_rz S (n+2) _ hp,one_mul]
    exact BDL26RZDecoderAdapter.rzStepOutput_weight S (n+2) _ hp s
end QEC.Coding.BDL26PairedHistoryQueryCone
