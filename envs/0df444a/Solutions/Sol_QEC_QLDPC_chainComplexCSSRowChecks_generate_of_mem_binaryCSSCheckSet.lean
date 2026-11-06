-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSRowChecks_generate_of_mem_binaryCSSCheckSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:40:04.112239+00:00
-- url     : https://prove2.me/submissions/1bec167e-c26a-40a6-98e1-c22ba0bb5abe

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_generate_cssXCheck_of_mem_firstCoboundaryCheckCode
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_generate_cssZCheck_of_mem_middleBoundaryCode

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι κ lambda : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda))
    {P : Coding.PauliSymplectic.Binary ι}
    (hP : P ∈ Coding.PauliSymplectic.binaryCSSCheckSet
      K.firstCoboundaryCheckCode K.middleBoundaryCode) :
    Coding.PauliSymplectic.GeneratedStabilizer
      (fun g : {Q : Coding.PauliSymplectic.Binary ι // Q ∈ chainComplexCSSRowChecks K} => g.1)
      P := by
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · exact chainComplexCSSRowChecks_generate_cssXCheck_of_mem_firstCoboundaryCheckCode K hx
  · exact chainComplexCSSRowChecks_generate_cssZCheck_of_mem_middleBoundaryCode K hz
end QEC.QLDPC
