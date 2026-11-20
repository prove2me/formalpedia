-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:26.487366+00:00
-- url     : https://prove2.me/submissions/0f114dec-92df-4b68-a803-9880cb903f84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_parity_other

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) :=
  one_parity_endpoint S h q (edge_parity_other S q e h hh) hb
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
