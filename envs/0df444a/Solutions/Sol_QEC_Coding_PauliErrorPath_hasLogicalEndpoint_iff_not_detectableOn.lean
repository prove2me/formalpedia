-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.hasLogicalEndpoint_iff_not_detectableOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:16.132659+00:00
-- url     : https://prove2.me/submissions/d969f60d-e2dc-4043-a35c-019bb3205b6c

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Theorems.Thm_QEC_Coding_StabilizerCode_not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath
namespace QEC.Coding.PauliErrorPath
theorem _root_.solution
    (γ : PauliErrorPath (ι := ι)) (Q : StabilizerCode.SourceValidBinary ι) :
    γ.HasLogicalEndpoint Q ↔
      ¬ Semantics.DetectableOn Q.1.code (toQubitOperator γ.endpoint) := by
  exact
    (StabilizerCode.not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
      Q γ.endpoint).symm
end QEC.Coding.PauliErrorPath
