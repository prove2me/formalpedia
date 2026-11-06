-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:26:18.931325+00:00
-- url     : https://prove2.me/submissions/3581af5a-0544-4b49-8c38-f06bcee93bc6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryMul_upToSign_binaryMul_dagger_left

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
    StabilizerEquivalent generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by
  constructor
  · rintro ⟨S, hS, hRelative⟩
    exact ⟨S, hS,
      binaryUpToSign_trans (binaryMul_upToSign_binaryMul_dagger_left E F) hRelative⟩
  · rintro ⟨S, hS, hProduct⟩
    exact ⟨S, hS,
      binaryUpToSign_trans
        (binaryUpToSign_symm (binaryMul_upToSign_binaryMul_dagger_left E F)) hProduct⟩
end QEC.Coding.PauliSymplectic
