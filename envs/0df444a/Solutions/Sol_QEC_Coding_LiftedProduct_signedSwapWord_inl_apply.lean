-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:25:37.791844+00:00
-- url     : https://prove2.me/submissions/5275cfeb-3e1a-4754-8a81-41a84ae1ec05

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (b : B) :
    signedSwapWord z (Sum.inl b) = z (Sum.inr b) := rfl
end QEC.Coding.LiftedProduct
