-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocal_region_parity_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:49:50.870243+00:00
-- url     : https://prove2.me/submissions/fcbe9c65-6193-424b-982e-2258d349b1a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_parity_weight_le
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_weight_eq_regions

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    (∑ face : XStarFace P x,
      (bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 1)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 1)))) ≤
      HammingWeight syndrome := by
  rw [xLocal_weight_eq_regions P A4 R x S]
  apply Finset.sum_le_sum
  intro face _
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (xLocal_parity_weight_le _) (xLocal_parity_weight_le _))
      (xLocal_parity_weight_le _)) (xLocal_parity_weight_le _)
end QEC.Coding.BDL26RXLocalReplacement
