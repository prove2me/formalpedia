-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.tanner_d1_d0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:33:47.708321+00:00
-- url     : https://prove2.me/submissions/1cfd76f3-f379-461b-b02f-9778749f1d32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_tannerCoboundary_squared


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (P : TannerSquarePresentation) (p : Word F P.X) :
    tannerCoboundary1 P (tannerCoboundary0 P p) = 0 :=
  LinearMap.congr_fun (tannerCoboundary_squared P) p
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
