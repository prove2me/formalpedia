-- Prove2me | solution 2 for QEC.Coding.PauliSymplectic.mem_scopedErrorFamily_sameSpaceErrorSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:46.210099+00:00
-- url     : https://prove2.me/submissions/bee58380-6ec8-4f54-b0fe-890e457a61c3

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_scopedErrorFamily_sameSpaceErrorSet

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
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet ↔
      E ∈ scopedErrorOperators (ι := ι) B := by
  rw [scopedErrorFamily_sameSpaceErrorSet]
end QEC.Coding.PauliSymplectic
