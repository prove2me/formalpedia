-- Prove2me | solution 2 for QEC.Coding.PauliSymplectic.degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:46.628495+00:00
-- url     : https://prove2.me/submissions/59a0e293-7255-4327-b397-fceacac63c78

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    DegenerateErrorPair generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by
  exact stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign generators E F
end QEC.Coding.PauliSymplectic
