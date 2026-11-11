-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.query_edge_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:11:48.090117+00:00
-- url     : https://prove2.me/submissions/e368366e-c439-44f1-8892-4d22a74b90c0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_step

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) (z : Coordinates S n i.castSucc)
    (hz : z ∈ queries S n e a i.castSucc) (p : Coordinates S n i.succ)
    (hp : p ∈ coarseRead S (n+2) (LevelTwoHistory.physicalStep i) z) :
    p ∈ queries S n e a i.succ := by
  rw [queries_step S n e a i ha]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z,hz,hp⟩)
end QEC.Coding.BDL26PairedHistoryQueryCone
