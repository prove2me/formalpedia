-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:53:12.224561+00:00
-- url     : https://prove2.me/submissions/8490e2bb-41c8-4ffb-9770-c904aa42a89a

-- ID: a036031d-b0a6-438a-ba3b-2da317eece3b | NAME: QEC.Coding.PauliSymplectic.degenerateErrorPair_iff_binaryMul_mem_generated_upToSign | 未本地编译验证
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
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

theorem solution
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    DegenerateErrorPair generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by
  simp only [DegenerateErrorPair, StabilizerEquivalent, InGeneratedStabilizerUpToSign,
    BinaryUpToSign]
  constructor
  · rintro ⟨S, hS, hvec⟩
    exact ⟨S, hS, by simpa [binaryMul, binaryDagger] using hvec⟩
  · rintro ⟨S, hS, hvec⟩
    exact ⟨S, hS, by simpa [binaryMul, binaryDagger] using hvec⟩
