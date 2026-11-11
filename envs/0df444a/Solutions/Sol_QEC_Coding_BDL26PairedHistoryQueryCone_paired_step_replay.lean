-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.paired_step_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:30:15.825936+00:00
-- url     : https://prove2.me/submissions/4401a5d5-6df7-4467-8dfd-b3a2d7dc96e2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_potential_support
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correctionQueries_subset
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_query_agreement
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correction_pair_replay


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) (s t : TopInput S n)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val)
    (i : StepIndex n) (ha : a.val ≤ i.val) :
    (actualOutput S n s i).correction + (actualOutput S n (perturbTop S n s e) i).correction =
      (actualOutput S n t i).correction + (actualOutput S n (perturbTop S n t e) i).correction := by
  apply correction_pair_replay S (n+2) (LevelTwoHistory.physicalStep i)
    (potential S n e i.succ)
  · exact potential_support S n s e i.succ
  · exact potential_support S n t e i.succ
  · exact fun p hp => query_agreement S n e a s t htop i.succ
      (by change a.val ≤ i.val+1; omega) p
      (correctionQueries_subset S n e a i ha hp)
  · exact fun p hp => query_agreement S n e a (perturbTop S n s e)
      (perturbTop S n t e) hflip i.succ (by change a.val ≤ i.val+1; omega) p
        (correctionQueries_subset S n e a i ha hp)
end QEC.Coding.BDL26PairedHistoryQueryCone
