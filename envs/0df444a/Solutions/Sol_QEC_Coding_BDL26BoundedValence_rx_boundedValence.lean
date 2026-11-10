-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.rx_boundedValence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:19:01.502349+00:00
-- url     : https://prove2.me/submissions/f0c4201f-c76c-473b-b75e-1c2f36932650

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rx_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) :=
  BDL26RXLocalReplacement.rx_boundedValence P A4 R S h
end QEC.Coding.BDL26BoundedValence
