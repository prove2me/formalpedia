-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actual_assembled_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:33:00.992445+00:00
-- url     : https://prove2.me/submissions/90db5162-3636-4a62-9cfd-abc452cd196b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_balance_full_word
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_interval_word
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_split
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
    descentWord S n b u c hcb + assembledPrefix S n sigma c =
      intervalMap1 (SuffixData S n) a c hac
        (descentWord S n b u a (hac.trans hcb) + assembledPrefix S n sigma a) +
        (SuffixData S n).family.coboundary0 c
          (accumulatedPotential S n b u a c.val hcb hac) := by
  rw [assembledPrefix_split S n sigma a c hac,map_add]
  exact balance_full_word _ _ _ _ _ (actual_interval_word S n sigma b u hu a c hac hcb)
end QEC.Coding.BDL26HistoryErrorTelescoping
