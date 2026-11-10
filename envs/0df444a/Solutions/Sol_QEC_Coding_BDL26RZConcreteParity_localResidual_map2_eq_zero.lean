-- Prove2me | solution 1 for QEC.Coding.BDL26RZConcreteParity.localResidual_map2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:54:09.918211+00:00
-- url     : https://prove2.me/submissions/51542afa-a3f8-4ee9-8023-5a9d785f6524

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_map2
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockPart_map2

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RZConcreteParity
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z)
    (z : P.Z) :
    blockPart P S z (map2Coord P A S s) +
      rootLift P A S z (blockParity P S (map2Coord P A S s) z) = 0 := by
  rw [blockParity_map2, blockPart_map2]
  funext t
  exact CharTwo.add_self_eq_zero (rootLift P A S z (s z) t)
end QEC.Coding.BDL26RZConcreteParity
