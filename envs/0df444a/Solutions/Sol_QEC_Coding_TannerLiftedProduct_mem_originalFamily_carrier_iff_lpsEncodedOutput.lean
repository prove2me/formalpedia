-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.mem_originalFamily_carrier_iff_lpsEncodedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:05:34.927876+00:00
-- url     : https://prove2.me/submissions/6d9bfb67-0de9-44f7-88a6-f790d5fa9caa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_carrier_iff_lpsEncodedOutput
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyIndex_decode_original


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_307
open FiniteFieldPauli
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p D r r' s : ℕ}
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (ψ : Semantics.Qudit.QuditRegister (fun _ : LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r')
      PSL(2, ZMod (lpsResiduePrimeSequence hp hp4 n).q) => Fintype.card F)) :
    ψ ∈ (semanticPresentation (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j))
      h h').code.carrier ↔
      ∀ i, lpsEncodedOutputOperator e (encodedFieldTables e)
        (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j))
        (h.map e.symm) (h'.map e.symm) i ψ = ψ := by
  have hLabel :
      (fun j => (lpsPSLEnumerationEquiv (lpsResiduePrimeSequence hp hp4 n).q)
        (lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j))) =
      (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j)) :=
    funext (fun j => lpsEffectiveQuaternionFamilyIndex_decode_original hp hp4 n (generators j))
  have hCarrier := congrArg (fun label => ψ ∈ (semanticPresentation label h h').code.carrier) hLabel
  exact (Iff.of_eq hCarrier.symm).trans
    (mem_carrier_iff_lpsEncodedOutput e
      (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' ψ)
end QEC.Coding.TannerLiftedProduct
