-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalRadialParity.radialGauge_connectingWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:54:47.609046+00:00
-- url     : https://prove2.me/submissions/cdba6f04-1b61-4acb-b402-c28d568ace6f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_connectingWeight_sum_le
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_eq_zero_of_other
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalRadialParity
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field) :
    connectingWeight P A x S (radialGauge P A x S selected alpha) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold radialGauge
  apply (xLocal_connectingWeight_sum_le P A x S _).trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro q _
  exact connectingWeight_single_eq_zero_of_other P A x S _ rfl rfl _
end QEC.Coding.BDL26XLocalRadialParity
