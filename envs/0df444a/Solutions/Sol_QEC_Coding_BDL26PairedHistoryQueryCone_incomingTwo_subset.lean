-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.incomingTwo_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:20:03.801253+00:00
-- url     : https://prove2.me/submissions/40357242-5fb1-4684-9fa2-74971d45bf76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_distance_le_two_mem_forwardTwo
import Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_mem_forwardTwo
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (v : V) :
    xiIndexSet G v 2 ⊆ forwardTwo (reverseGraph G) v := by
  intro u hu
  have hp := distance_le_two_mem_forwardTwo G u v (Finset.mem_filter.mp hu).2
  rcases (mem_forwardTwo G u v).mp hp with he | he | ⟨w,huw,hwv⟩
  · exact (mem_forwardTwo _ _ _).mpr (Or.inl he.symm)
  · exact (mem_forwardTwo _ _ _).mpr (Or.inr (Or.inl he))
  · exact (mem_forwardTwo _ _ _).mpr (Or.inr (Or.inr ⟨w,hwv,huw⟩))
end QEC.Coding.BDL26PairedHistoryQueryCone
