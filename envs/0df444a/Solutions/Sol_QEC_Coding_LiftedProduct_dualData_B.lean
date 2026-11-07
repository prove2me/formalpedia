-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.dualData_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:26:03.760925+00:00
-- url     : https://prove2.me/submissions/c58178a0-a874-42e9-8c74-a862445b831b

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {F G aRow aCol bRow bCol : Type*}
    [Semiring F] [Group G]
    (D : Data F G aRow aCol bRow bCol) :
    (dualData D).B = starTranspose D.B := rfl
end QEC.Coding.LiftedProduct
