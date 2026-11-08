-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:19:04.761641+00:00
-- url     : https://prove2.me/submissions/54278e98-00f8-416c-a8dc-bf7154b97328

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) (v:ℕ) (hv:v∈entries a ts):
 v<Fintype.card PSL(2,ZMod a.q):=by
 have hlen: (lpsPSLList a.q).length=Fintype.card PSL(2,ZMod a.q):=LPSOriginalPSLLookupMachine.original_length_card a.q
 rcases List.mem_cons.mp hv with he|hg
 · subst v
   exact (lpsPSLIndexOne a.q).isLt.trans_le hlen.le
 · rcases List.mem_map.mp hg with ⟨t,_,he⟩
   subst v
   exact (result a t).isLt.trans_le hlen.le
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
