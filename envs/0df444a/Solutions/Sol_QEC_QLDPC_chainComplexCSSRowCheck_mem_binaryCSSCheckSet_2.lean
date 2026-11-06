-- Prove2me | solution 2 for QEC.QLDPC.chainComplexCSSRowCheck_mem_binaryCSSCheckSet
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:40:53.200936+00:00
-- url     : https://prove2.me/submissions/8724d0a7-9599-4aab-bcd9-ba768a8db219

-- ID: 54dbb0d6-95c0-4c01-9a0c-43b0017bbe1f | NAME: QEC.QLDPC.chainComplexCSSRowCheck_mem_binaryCSSCheckSet | 未本地编译验证
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem solution
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (c : Sum κ lambda) :
    chainComplexCSSRowCheck K c ∈
      Coding.PauliSymplectic.binaryCSSCheckSet
        K.firstCoboundaryCheckCode K.middleBoundaryCode := by
  classical
  change (∃ x : Coding.Word (ZMod 2) ι,
      x ∈ K.firstCoboundaryCheckCode.carrier ∧
        chainComplexCSSRowCheck K c = Coding.PauliSymplectic.cssXCheck x) ∨
    (∃ z : Coding.Word (ZMod 2) ι,
      z ∈ K.middleBoundaryCode.carrier ∧
        chainComplexCSSRowCheck K c = Coding.PauliSymplectic.cssZCheck z)
  rcases c with k | l
  · left
    refine ⟨Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := ZMod 2) k), ?_, rfl⟩
    rw [QEC.Coding.ChainComplexData.mem_firstCoboundaryCheckCode_iff]
    exact ⟨Coding.canonicalBasisWord (F := ZMod 2) k, rfl⟩
  · right
    refine ⟨K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l), ?_, rfl⟩
    rw [QEC.Coding.ChainComplexData.mem_middleBoundaryCode_iff]
    exact ⟨Coding.canonicalBasisWord (F := ZMod 2) l, rfl⟩
