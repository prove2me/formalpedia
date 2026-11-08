-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decode_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:30:06.239997+00:00
-- url     : https://prove2.me/submissions/4a7af3ad-779a-4368-b6d6-4153c921041a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encodeFields


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
open LPSSparseEmitterRow
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
theorem _root_.solution {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeFields (LPSSparseEmitterCodec.fields (checks a g t h h'))=some (checks a g t h h'):=
 LPSSparseEmitterCodec.decode_encodeFields _
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
