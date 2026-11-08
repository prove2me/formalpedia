-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource.decodeTyped_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:08:55.764174+00:00
-- url     : https://prove2.me/submissions/237f3c16-05eb-4003-b29b-4c107c64789f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decodeTyped_encode


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
theorem _root_.solution {p D r r' s:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList a.q).length)+(2*r)*((2*r')*(lpsPSLList a.q).length)) s (output a g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>LPSOriginalGeneratorIndexMachine.result a (g j)) h h'):=
 LPSSparseEmitterCodec.decodeTyped_encode _
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterSource
