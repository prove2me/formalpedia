-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualInputs_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:45:28.232592+00:00
-- url     : https://prove2.me/submissions/859070f9-e654-4476-841b-91eb5b872603

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_comp
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    prefixInput (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b.val
      (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a hab = actualInputs S n sigma a :=
  (prefixInput_comp (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) n (Nat.le_refl _)
    sigma b a (Nat.le_of_lt_succ b.isLt) hab).symm
end QEC.Coding.BDL26HistoryErrorTelescoping
