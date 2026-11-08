-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_sourceValid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:49:18.466458+00:00
-- url     : https://prove2.me/submissions/e758531f-1f61-453e-8097-3fb4416a1780

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_FiberBundle_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_LiftedProduct_binaryCSSCode_stabilizer_isSourceValidBinary


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    ((balancedSubsystem q hq40 hq).complex.binaryCSSCode).stabilizer.IsSourceValidBinary :=
  ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary
    (balancedSubsystem q hq40 hq).complex
end QEC.Coding.BalancedProduct.BE20Balanced
