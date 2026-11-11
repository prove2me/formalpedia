-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:18:18.991934+00:00
-- url     : https://prove2.me/submissions/21717a83-ee77-44bf-a8d3-8c2fade3f3ea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_errorDown_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b) :
    descentWord S n b u b (Nat.le_refl _) = u := errorDown_self S n b.val _ u
end QEC.Coding.BDL26HistoryErrorTelescoping
