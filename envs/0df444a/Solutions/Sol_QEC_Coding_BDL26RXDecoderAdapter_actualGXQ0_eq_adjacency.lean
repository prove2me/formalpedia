-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.actualGXQ0_eq_adjacency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:44:46.98227+00:00
-- url     : https://prove2.me/submissions/0a1d6e85-a34e-411d-842c-5c21f96c47ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxXQAdjacency_eq_sum_coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    actualGXQ0 P A S = rxXQAdjacency P := by
  apply LinearMap.ext
  intro w
  funext q
  exact (rxXQAdjacency_eq_sum_coordinates P A S w q).symm
end QEC.Coding.BDL26RXDecoderAdapter
