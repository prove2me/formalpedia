-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.mem_originalFamily_carrier_iff_decodedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:25:00.866106+00:00
-- url     : https://prove2.me/submissions/a950a94b-2a4f-4d08-b1d9-5ac357d31814

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_decodedOperator_output
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_originalFamily_carrier_iff_lpsEncodedOutput


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
open FiniteFieldPauli
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily._p2m_local_instance_6058dbc402_120
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
theorem _root_.solution {p D r r' s:ℕ} {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p)
 (h:Matrix (Fin r) (Fin D) F) (h':Matrix (Fin r') (Fin D) F)
 (ψ:Semantics.Qudit.QuditRegister (fun _:LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod (lpsResiduePrimeSequence hp hp4 B).q)=>Fintype.card F)):
 ψ∈(semanticPresentation (fun j=>lpsQuaternionFamilyLabel hp hp4 B (g j)) h h').code.carrier↔
 ∀ i,decodedOperator e (encodedFieldTables e) i
 (output hp hp4 B g (encodedFieldTables e) (h.map e.symm) (h'.map e.symm)) ψ=ψ:=by
 have hc:=mem_originalFamily_carrier_iff_lpsEncodedOutput e hp hp4 B g h h' ψ
 exact hc.trans (by
  constructor
  · intro hall i
    exact (congrArg (fun op=>op ψ) (decodedOperator_output e hp hp4 B g h h' i)).trans (hall i)
  · intro hall i
    exact (congrArg (fun op=>op ψ) (decodedOperator_output e hp hp4 B g h h' i)).symm.trans (hall i))
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
