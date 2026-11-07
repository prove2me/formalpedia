-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.dualData_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:26:00.023648+00:00
-- url     : https://prove2.me/submissions/d76b4139-5e1e-4010-ba23-bdb593326dd9

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
    (dualData D).A = starTranspose D.A := rfl
end QEC.Coding.LiftedProduct
