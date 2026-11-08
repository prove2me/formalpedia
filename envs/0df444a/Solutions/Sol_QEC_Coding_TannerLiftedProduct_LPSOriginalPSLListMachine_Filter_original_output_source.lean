-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.original_output_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:03:40.521193+00:00
-- url     : https://prove2.me/submissions/75b8aed3-48ed-4a63-b2cf-ee3946f6715b

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_mapped_original_representatives


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter._p2m_local_instance_e75c5360c0_157
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
theorem _root_.solution (q:ℕ) [Fact q.Prime]:
 (representatives q (lpsSLList q)).map (quotient q)=lpsPSLList q:=mapped_original_representatives q
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
