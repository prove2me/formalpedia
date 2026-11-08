-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:54:02.362628+00:00
-- url     : https://prove2.me/submissions/72fa043b-6963-4bfc-b05f-c82290b93ee2

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine._p2m_local_instance_8252a2e3b6_28
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
theorem _root_.solution (p:ℕ):Function.Injective (fun a:LPSResiduePrime p=>unary a.q):=lpsResiduePrime_unary_injective p
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
