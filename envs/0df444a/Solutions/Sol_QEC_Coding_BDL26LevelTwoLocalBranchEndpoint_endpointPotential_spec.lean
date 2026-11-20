-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.endpointPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:43.255231+00:00
-- url     : https://prove2.me/submissions/7b706d3b-60d5-4699-a1b4-e167f1f110b1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (h : Error S) (a : (P S).Q)
    (ha : ∀ q, q≠a → parity S h q=0) (hb : localSuccess S (delta S h)) :
    boundary S (endpointPotential S h a ha hb)=h+D S 0+D S (delta S h) :=
  Classical.choose_spec (one_parity_endpoint S h a ha hb)
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
