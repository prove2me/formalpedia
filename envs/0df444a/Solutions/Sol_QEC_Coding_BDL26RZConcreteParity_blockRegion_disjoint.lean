-- Prove2me | solution 1 for QEC.Coding.BDL26RZConcreteParity.blockRegion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:53:35.111306+00:00
-- url     : https://prove2.me/submissions/7f5a8805-c528-4897-b052-f528b71e8c88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberRegion_disjoint


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RZConcreteParity
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    {z w : P.Z} (h : z ≠ w) : Disjoint (blockRegion P S z) (blockRegion P S w) :=
  fiberRegion_disjoint (fun t : RZZ P S => t.1) h
end QEC.Coding.BDL26RZConcreteParity
