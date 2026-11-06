-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.mem_scopedErrorFamily_sameSpaceErrorSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:53:05.203198+00:00
-- url     : https://prove2.me/submissions/fa64767a-5c81-48c5-99f0-c7efc4f9bda2

-- ID: fa600099-2581-4931-a27d-ff598d6a803e | NAME: QEC.Coding.PauliSymplectic.mem_scopedErrorFamily_sameSpaceErrorSet_iff | 未本地编译验证
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

theorem solution (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet ↔
      E ∈ scopedErrorOperators (ι := ι) B := by
  simp only [QEC.Semantics.FiniteKrausFamily.sameSpaceErrorSet, Set.mem_range,
    QEC.Coding.PauliSymplectic.scopedErrorOperators, Set.mem_image,
    QEC.Coding.PauliSymplectic.scopedErrorFamily]
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.1, P.2, hP⟩
  · rintro ⟨P, hP, hPE⟩
    exact ⟨⟨P, hP⟩, hPE⟩
