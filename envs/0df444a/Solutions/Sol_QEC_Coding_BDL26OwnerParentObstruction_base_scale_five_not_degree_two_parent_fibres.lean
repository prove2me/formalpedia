-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerParentObstruction.base_scale_five_not_degree_two_parent_fibres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:12:44.955711+00:00
-- url     : https://prove2.me/submissions/25957469-9061-4520-84a7-e5bd413f0352

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_not_rz_after_rx_degree_two_parent_fibres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerParentObstruction
theorem _root_.solution :
    let P := baseTannerSquarePresentation
    let S := scaleFive
    let A := (rxState S baseState).admissible
    ¬ (∀ (source : (rxReplacementPresentation P S).Z)
      (target : RZZ (rxReplacementPresentation P S) S),
      map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) =
        some (rxSyndromeOwner P S source)) :=
  not_rz_after_rx_degree_two_parent_fibres baseTannerSquarePresentation scaleFive
    (rxState scaleFive baseState).admissible
    (0 : BDL26FiniteAlternatingCore.BaseX) baseLocalFace
end QEC.Coding.BDL26OwnerParentObstruction
