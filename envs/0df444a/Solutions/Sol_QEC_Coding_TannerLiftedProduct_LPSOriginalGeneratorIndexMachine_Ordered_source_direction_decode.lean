-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_direction_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:16:15.657519+00:00
-- url     : https://prove2.me/submissions/d1590e4d-81fd-4724-967d-0a010a3a5180

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_result_decode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered._p2m_local_instance_8252a2e3b6_393
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
theorem _root_.solution {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)):
 (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
 (result (lpsEffectiveResiduePrimeAt hp hp4 n) (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j))=
 lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j:=by
 rw [result_decode]
 rfl
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
