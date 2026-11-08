-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.sourcePhysicalSize_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:30:17.500224+00:00
-- url     : https://prove2.me/submissions/9ca2981a-b345-4883-93ee-91234a807ee4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveVertexGroup_card_cofinal


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
theorem _root_.solution {p r r':ℕ} (hp:p.Prime) (hp4:p%4=1):
 ∀ N:ℕ,∃ B,N ≤ physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) (p+1) r r':=by
 intro N
 obtain ⟨B,hB⟩:=lpsEffectiveVertexGroup_card_cofinal hp hp4 N
 exact ⟨B,hB.trans (carrier_le_physicalSize _ (by omega))⟩
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
