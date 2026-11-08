-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzCzH2Coordinate_bijective_iff_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:06:57.875376+00:00
-- url     : https://prove2.me/submissions/db6854ad-56f6-47cd-b8b0-982c01353bba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_surjective
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker

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
    Function.Bijective (rzCzH2Coordinate P z S) ↔
      LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
        LinearMap.ker totalParity := by
  constructor
  · intro hbijective
    exact (rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
      P z S).1 hbijective.1
  · intro hrange
    exact ⟨(rzCzH2Coordinate_injective_iff_range_eq_totalParity_ker
      P z S).2 hrange, rzCzH2Coordinate_surjective P A z S⟩
end QEC.Coding.BDL26RZLocalReplacement
