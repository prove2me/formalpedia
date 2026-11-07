-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:58:43.786866+00:00
-- url     : https://prove2.me/submissions/6251b5ce-1285-4b82-896a-376ee256867e

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {F : Type u} [Zero F] [DecidableEq F]
    {ι : Type v} [Fintype ι] (z : Word F ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]
end QEC.Coding.BalancedProduct.PKDistance
