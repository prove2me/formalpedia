-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:41.555548+00:00
-- url     : https://prove2.me/submissions/b1b0b49f-7044-4a52-8361-f94bfc3eeee3

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution {F A B : Type*}
    (z : Word F (Sum A B)) (a : A) :
    swapWord z (Sum.inr a) = z (Sum.inl a) := rfl
end QEC.Coding.BalancedProduct.LiftedProductDuality
