-- Prove2me | solution 1 for QEC.Coding.BDL26RZConcreteParity.sum_rootLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:53:58.917589+00:00
-- url     : https://prove2.me/submissions/97434f89-ad62-478d-8953-a0b282158489

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockPart_map2
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_sum_fiberPart


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RZConcreteParity
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) :
    (∑ z : P.Z, rootLift P A S z (s z)) = map2Coord P A S s := by
  simp_rw [← blockPart_map2]
  exact sum_fiberPart (fun t : RZZ P S => t.1) (map2Coord P A S s)
end QEC.Coding.BDL26RZConcreteParity
