-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.lifted_actual_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:11:09.301207+00:00
-- url     : https://prove2.me/submissions/156fa6f2-adfd-431e-bf4a-be2a914364bd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearMap_list_sum
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_components
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (i : StepIndex n)
    (b : LevelIndex n) (hib : i.succ.val ≤ b.val) :
    intervalMap1 (SuffixData S n) i.succ b hib (actualOutput S n sigma i).correction =
      ((actualOutput S n sigma i).localComponents.map
        (intervalMap1 (SuffixData S n) i.succ b hib)).sum := by
  rw [snapshotWords_components]
  exact (linearMap_list_sum _ _).symm
end QEC.Coding.BDL26HistoryErrorTelescoping
