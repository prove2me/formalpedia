-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:05:11.224943+00:00
-- url     : https://prove2.me/submissions/a9966f16-ea4f-4072-b436-c4319b41b58e

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.Cyclic
theorem _root_.solution
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (r c : Unit) :
    (liftedProductData A x).B r c = cyclicBoundaryElement x := rfl
end QEC.Coding.BalancedProduct.Cyclic
