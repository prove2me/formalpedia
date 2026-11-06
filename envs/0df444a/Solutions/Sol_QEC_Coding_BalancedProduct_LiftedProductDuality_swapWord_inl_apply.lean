-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:53.106254+00:00
-- url     : https://prove2.me/submissions/a7d2697d-9aa3-4338-ac40-201fead4e454

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
    (z : Word F (Sum A B)) (b : B) :
    swapWord z (Sum.inl b) = z (Sum.inr b) := rfl
end QEC.Coding.BalancedProduct.LiftedProductDuality
