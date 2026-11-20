-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.successful_nonzero_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:53.819222+00:00
-- url     : https://prove2.me/submissions/80d2dbe0-bbe2-4d5c-ad6e-11392a7b78c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (s : Syndrome S)
    (hs : localSuccess S s) (hne : s≠0) : D S s≠0 := by
  obtain ⟨w,hw⟩ := hs
  have hd := (returned_local_and_syndrome S s w hw).2
  intro hz
  have hdelta : delta S (D S s)=delta S (0 : Error S) := congrArg (delta S) hz
  have hzero : delta S (0 : Error S)=0 := (delta S).map_zero
  exact hne (hd.symm.trans (hdelta.trans hzero))
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
