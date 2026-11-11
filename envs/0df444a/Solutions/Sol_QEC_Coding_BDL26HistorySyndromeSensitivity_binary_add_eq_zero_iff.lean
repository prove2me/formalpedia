-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.binary_add_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:29:24.773194+00:00
-- url     : https://prove2.me/submissions/92ea5924-4cdb-4ab1-870b-d4c0eea33658

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (a b : BDL26Field) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = (a + b) + b := by rw [add_assoc, ZModModule.add_self, add_zero]
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact ZModModule.add_self _
end QEC.Coding.BDL26HistorySyndromeSensitivity
