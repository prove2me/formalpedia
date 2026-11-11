-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:26:33.752037+00:00
-- url     : https://prove2.me/submissions/d7893851-76cb-4bdb-8261-498e77c870e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_zero_eq
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
    (a : LevelIndex n) (hab : a.val ≤ b.val) :
    accumulatedPotential S n b u a a.val hab (Nat.le_refl _) = 0 := by
  rcases a with ⟨a,ha⟩
  cases a with
  | zero => exact accumulatedPotential_zero_eq S n b u ⟨0,ha⟩ (Nat.le_refl _)
  | succ c =>
      rw [accumulatedPotential_succ_eq,dif_pos rfl]
end QEC.Coding.BDL26HistoryErrorTelescoping
