-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actual_interval_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:26:17.501166+00:00
-- url     : https://prove2.me/submissions/2a4382c1-d553-4151-b372-e37852ddd200

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_interval_word_nat
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a c : LevelIndex n) (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    intervalMap1 (SuffixData S n) a c hac (descentWord S n b u a (hac.trans hcb)) =
      descentWord S n b u c hcb + correctionIntervalSum S n sigma a c +
        (SuffixData S n).family.coboundary0 c
          (accumulatedPotential S n b u a c.val hcb hac) :=
  actual_interval_word_nat S n sigma b u hu c.val hcb a hac
end QEC.Coding.BDL26HistoryErrorTelescoping
