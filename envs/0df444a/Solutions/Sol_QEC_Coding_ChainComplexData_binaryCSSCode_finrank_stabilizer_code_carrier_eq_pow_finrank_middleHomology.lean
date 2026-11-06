-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:51:59.074448+00:00
-- url     : https://prove2.me/submissions/3723a2f0-cae0-4c14-82c4-7efaf063e05f

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier
import Theorems.Thm_QEC_Coding_ChainComplexData_length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.ChainComplexData
namespace QEC.Coding.ChainComplexData
theorem _root_.solution
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) K.middleHomology := by
  rw [binaryCSSCode]
  change Module.finrank Complex
      (PauliSymplectic.binaryCSSQuantumCodeOfDualLe K.firstCoboundaryCheckCode
        K.middleBoundaryCode K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual).carrier =
    2 ^ Module.finrank (ZMod 2) K.middleHomology
  rw [PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  rw [K.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology]
end QEC.Coding.ChainComplexData
