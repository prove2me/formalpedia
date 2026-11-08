-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.decodeTyped_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:10.088273+00:00
-- url     : https://prove2.me/submissions/ba758c1e-f538-4fb2-b940-8a351acadacd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterSource_decodeTyped_output


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
theorem _root_.solution {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 LPSSparseEmitterCodec.decodeTyped
 (D*(D*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)+
 (2*r)*((2*r')*(lpsPSLList (lpsEffectiveResiduePrimeAt hp hp4 B).q).length)) s (output hp hp4 B g t h h')=
 some (lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h'):=
 LPSSparseEmitterSource.decodeTyped_output _ g t h h'
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
