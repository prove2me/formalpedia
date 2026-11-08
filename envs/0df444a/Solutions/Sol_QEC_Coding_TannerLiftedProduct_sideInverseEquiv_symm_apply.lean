-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:01:15.157327+00:00
-- url     : https://prove2.me/submissions/6ebf74d1-98e5-47b0-b199-5b774db6d412

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq G]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : Fin 2 × G) :
    sideInverseEquiv.symm x = (oppositeSide x.1, x.2⁻¹) := rfl
end QEC.Coding.TannerLiftedProduct
