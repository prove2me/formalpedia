-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:01:36.852118+00:00
-- url     : https://prove2.me/submissions/a75a4e5e-7bbe-4458-8b43-8003973aa6c1

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
    sideInverseEquiv x = (oppositeSide x.1, x.2⁻¹) := rfl
end QEC.Coding.TannerLiftedProduct
