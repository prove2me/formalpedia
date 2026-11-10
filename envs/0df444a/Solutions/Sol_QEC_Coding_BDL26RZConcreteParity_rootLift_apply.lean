-- Prove2me | solution 1 for QEC.Coding.BDL26RZConcreteParity.rootLift_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:53:53.171636+00:00
-- url     : https://prove2.me/submissions/b251fb11-64ee-402b-96c4-6670a8f15a2a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rzMap2_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RZConcreteParity
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z w : P.Z) (b : BDL26Field) (v : ZDoubleCylinderVertex P w S) :
    rootLift P A S z b ⟨w,v⟩ =
      if v = rzMap1ZRoot P A w S then (Pi.single z b : Word BDL26Field P.Z) w else 0 :=
  rzMap2_apply P A S (Pi.single z b) w v
end QEC.Coding.BDL26RZConcreteParity
