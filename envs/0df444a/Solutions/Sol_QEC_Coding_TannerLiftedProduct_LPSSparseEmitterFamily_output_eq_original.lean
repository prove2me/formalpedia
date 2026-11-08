-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.output_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:30:15.691064+00:00
-- url     : https://prove2.me/submissions/7954a270-5fdb-4a0e-848c-bd714f8c4860

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
theorem _root_.solution {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 output hp hp4 B g t h h'=LPSSparseEmitterCodec.encode
 ((lpsEncodedCheckOutput t (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j)) h h').map
 (fun rs=>rs.map (fun e=>(e.1.val,e.2.val)))):=rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
