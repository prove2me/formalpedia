-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzXQH0ToH1_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:06:31.628289+00:00
-- url     : https://prove2.me/submissions/8661fd6d-e148-4410-8bfc-d944c5b867e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzXQDegreeZero_totalParity

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (cohomologyClass : RZXH0 P x) :
    rzCqH1Coordinate P q S
        (rzXQH0ToH1 P q x hxq S cohomologyClass) =
      (rzCxH0Coordinates P x cohomologyClass).1 +
        (rzCxH0Coordinates P x cohomologyClass).2 := by
  refine Submodule.Quotient.induction_on _ cohomologyClass ?_
  intro word
  change rzCqH1Coordinate P q S
      (rzXQH0ToH1 P q x hxq S
        ((LinearMap.range (rzCx P x).boundary1).mkQ word)) =
    (rzCxH0Coordinates P x
      ((LinearMap.range (rzCx P x).boundary1).mkQ word)).1 +
      (rzCxH0Coordinates P x
        ((LinearMap.range (rzCx P x).boundary1).mkQ word)).2
  rw [rzXQH0ToH1_mk, rzCxH0Coordinates_mk]
  change totalParity (rzXQDegreeZero P q x hxq S word) =
    word 0 + word 1
  exact rzXQDegreeZero_totalParity P q x hxq S word
end QEC.Coding.BDL26RZLocalReplacement
