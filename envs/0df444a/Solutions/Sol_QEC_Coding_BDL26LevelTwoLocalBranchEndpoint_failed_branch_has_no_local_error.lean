-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.failed_branch_has_no_local_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:11:35.622311+00:00
-- url     : https://prove2.me/submissions/d582c6d4-2abf-4f7e-8dbb-00f4b5599534

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSearch_none_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (h : Error S)
    (hn : localSearch S (delta S h)=none) : ¬levelTwoLocalError S h := by
  intro hh
  exact (localSearch_none_iff S _).1 hn ⟨h,hh,rfl⟩
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
