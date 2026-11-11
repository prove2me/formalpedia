-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:26:36.63312+00:00
-- url     : https://prove2.me/submissions/ad77a63b-d8f7-4a73-a90f-873c951ad58d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_succ_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (i : StepIndex n) (hib : i.val < b.val) (hai : a.val ≤ i.val) :
    accumulatedPotential S n b u a (i.val+1) (by omega) (by omega) =
      ((SuffixData S n).selectedMap i).map0
        (accumulatedPotential S n b u a i.val (by omega) hai) + descentPotential S n b u i hib := by
  have hn : ¬ a.val = i.val+1 := by omega
  rw [accumulatedPotential_succ_eq]
  exact dif_neg hn
end QEC.Coding.BDL26HistoryErrorTelescoping
