-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.rxCount_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:46:26.33219+00:00
-- url     : https://prove2.me/submissions/e321d3bb-1a61-458d-8aba-6ef4d91c47ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rxCount_formula
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    rxCount a c = rxCount a b + rxCount b c := by
  rw [rxCount_formula _ _ (hab.trans hbc), rxCount_formula _ _ hab,
    rxCount_formula _ _ hbc]
  omega
end QEC.Coding.BDL26HistorySyndromeSensitivity
