-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSRowCheck_mem_binaryCSSCheckSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:38:04.34124+00:00
-- url     : https://prove2.me/submissions/af446b0a-9c18-44ce-8209-5e63645221c7

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (c : Sum κ lambda) :
    chainComplexCSSRowCheck K c ∈
      Coding.PauliSymplectic.binaryCSSCheckSet
        K.firstCoboundaryCheckCode K.middleBoundaryCode := by
  cases c with
  | inl k =>
      left
      refine ⟨_, ?_, rfl⟩
      exact (K.mem_firstCoboundaryCheckCode_iff _).2
        ⟨Coding.canonicalBasisWord (F := ZMod 2) k, rfl⟩
  | inr l =>
      right
      refine ⟨_, ?_, rfl⟩
      exact (K.mem_middleBoundaryCode_iff _).2
        ⟨Coding.canonicalBasisWord (F := ZMod 2) l, rfl⟩
end QEC.QLDPC
