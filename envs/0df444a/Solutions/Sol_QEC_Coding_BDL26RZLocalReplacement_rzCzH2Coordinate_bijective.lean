-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:45:19.994572+00:00
-- url     : https://prove2.me/submissions/c87a517b-6275-4a58-b5aa-4a3e758f1aa6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzTopCoboundary_range_eq_totalParity_ker

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    Function.Bijective (rzCzH2Coordinate P z S) :=
  (rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker P A z S).2
    (rzCzTopCoboundary_range_eq_totalParity_ker P A z S)
end QEC.Coding.BDL26RZLocalReplacement
