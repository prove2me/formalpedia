-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:26:02.729302+00:00
-- url     : https://prove2.me/submissions/fda7af44-4e96-4e78-9d1d-fd25de66b820

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution {F A B : Type*} [Neg F]
    (z : Word F (Sum A B)) (a : A) :
    signedSwapWord z (Sum.inr a) = -z (Sum.inl a) := rfl
end QEC.Coding.LiftedProduct
