-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.original_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:55:49.852336+00:00
-- url     : https://prove2.me/submissions/63c29acb-6b98-483d-94a8-92a0eebdb018

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_mapped_original_representatives


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine._p2m_local_instance_e75c5360c0_308
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
theorem _root_.solution (a:Input):
 (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.representatives a.val (lpsSLList a.val)).map (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.quotient a.val)=lpsPSLList a.val:=
 QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.mapped_original_representatives a.val
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
