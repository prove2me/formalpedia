-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.cleanedError_q_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:55:11.362303+00:00
-- url     : https://prove2.me/submissions/08adfc40-ec65-4a20-96ca-4f13c4c20f6e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_cleanedError_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_cover


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat) :
    SupportedOn (tailData S j).qCorrectionSector (cleanedError S j) := by
  intro p hp
  have hc := (tailData S j).correction_sectors_cover
  have hm : p ∈ correctionRegionUnion (rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)) ∪
      (tailData S j).qCorrectionSector := by rw [hc]; exact Finset.mem_univ p
  rcases Finset.mem_union.mp hm with hx | hq
  · obtain ⟨x, _, hpx⟩ := Finset.mem_biUnion.mp hx
    exact congrFun (cleanedError_x_zero S j x) ⟨p, hpx⟩
  · exact (hp hq).elim
end QEC.Coding.BDL26UniformRXTail
