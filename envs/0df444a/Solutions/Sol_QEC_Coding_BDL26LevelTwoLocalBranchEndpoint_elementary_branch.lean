-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.elementary_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:29.850028+00:00
-- url     : https://prove2.me/submissions/988787a0-d11c-435c-b8bf-5cfe21419d2a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_elementary_local

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (q : (C S).Q) :
    localSuccess S (delta S (canonicalBasisWord (F := Bit) q)) :=
  (localSuccess_iff S _).2 ⟨canonicalBasisWord (F := Bit) q,elementary_local S q,rfl⟩
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
