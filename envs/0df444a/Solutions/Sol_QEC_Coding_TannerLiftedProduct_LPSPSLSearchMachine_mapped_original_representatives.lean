-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.mapped_original_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:33:26.235874+00:00
-- url     : https://prove2.me/submissions/97155dc9-71bb-47ca-8043-e1daa5578321

import Definitions.Def_QEC_Coding_BitTuring_BooleanSwitch
import Definitions.Def_QEC_Coding_BitTuring_UnarySuffixEmpty
import Definitions.Def_QEC_Coding_BitTuring_UnaryTailProjection
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRetainedPrefixQueries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_mapped_representatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine._p2m_local_instance_25ca2d8bb9_350
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
theorem _root_.solution (q:ℕ) [Fact q.Prime]:
 (representatives q (lpsSLList q)).map (quotient q)=lpsPSLList q:=mapped_representatives q _
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
