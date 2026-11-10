-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxXQH0ToH1_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:05:49.861674+00:00
-- url     : https://prove2.me/submissions/c6e48390-8221-4be8-a865-5eb69b579bfb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_boundaryRoot_zeroCopy

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) (word : RXH0 P x S) :
    rxCqH1Coordinate P q S (rxXQH0ToH1 P A q x hxq S word) =
      rxCxH0Coordinate P A x S word := by
  change word.1
      (qToXDoubleCylinderVertex P A q x hxq S
        (0, Sum.inl (Sum.inl ()))) =
    word.1
      (0, (subdivisionOriginalBoundaryVertex P x S
        (A.xBoundaryRoot x)).1)
  exact rxCxCocycle_eq_boundaryRoot_zeroCopy
    P A x S word.1 word.2 _
end QEC.Coding.BDL26RXLocalReplacement
