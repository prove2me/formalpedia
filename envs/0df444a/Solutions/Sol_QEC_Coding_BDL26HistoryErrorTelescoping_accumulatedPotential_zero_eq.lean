-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:20:14.860617+00:00
-- url     : https://prove2.me/submissions/33ff1bf9-75a7-4212-8ccc-9a37206f8157

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n) (ha : a.val ≤ 0) :
    accumulatedPotential S n b u a 0 (Nat.zero_le _) ha = 0 := by
  rw [accumulatedPotential] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
