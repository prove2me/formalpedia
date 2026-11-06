-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryStabilizerCommonFixedQuantumCode_projector_fixed
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:41:57.10877+00:00
-- url     : https://prove2.me/submissions/8bae4d2c-b3d6-470e-b7ec-e9796a2c3173

-- ID: 1aef1601-8a4e-4f44-a06c-7a27c1c38490 | NAME: QEC.Coding.PauliSymplectic.binaryStabilizerCommonFixedQuantumCode_projector_fixed | 未本地编译验证
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

theorem solution (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ∀ P : Binary ι, P ∈ S →
      toQubitOperator P ((binaryStabilizerCommonFixedQuantumCode S).projector ψ) =
        (binaryStabilizerCommonFixedQuantumCode S).projector ψ := by
  intro P hP
  have hmem : (binaryStabilizerCommonFixedQuantumCode S).projector ψ ∈
      (binaryStabilizerCommonFixedQuantumCode S).carrier := by
    simpa [QEC.Semantics.QuantumCode.projector] using
      (Submodule.starProjection_apply_mem
        (binaryStabilizerCommonFixedQuantumCode S).carrier ψ)
  exact (QEC.Coding.PauliSymplectic.mem_binaryStabilizerCommonFixedQuantumCode_carrier S
    ((binaryStabilizerCommonFixedQuantumCode S).projector ψ)).1 hmem P hP
