-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.stoppingLevel_coalesces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:30:50.76902+00:00
-- url     : https://prove2.me/submissions/7684f89b-a481-42a6-a82b-47e008308bca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s : TopInput S n) (e : TopWord S n)
    (ha : 0 < (stoppingLevel S n s e).val) :
    actualInputs S n s (stoppingLevel S n s e) =
      actualInputs S n (perturbTop S n s e) (stoppingLevel S n s e) := by
  by_cases h : (coalescentLevels S n s e).Nonempty
  · have hs : stoppingLevel S n s e = (coalescentLevels S n s e).max' h := dif_pos h
    rw [hs]
    exact (Finset.mem_filter.mp (Finset.max'_mem _ h)).2
  · have hz : stoppingLevel S n s e = 0 := dif_neg h
    rw [hz] at ha
    change 0 < 0 at ha
    omega
end QEC.Coding.BDL26PairedHistoryQueryCone
