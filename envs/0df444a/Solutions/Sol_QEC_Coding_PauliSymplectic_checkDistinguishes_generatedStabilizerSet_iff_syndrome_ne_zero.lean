-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_generatedStabilizerSet_iff_syndrome_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:28:52.535775+00:00
-- url     : https://prove2.me/submissions/119454f9-c638-4b4c-bff5-a77784ddfa7c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_range_iff_syndrome_ne_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_generatedStabilizerSet_iff_range

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
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (generatedStabilizerSet generators) E ↔
      stabilizerSyndrome generators E ≠ 0 := by
  rw [checkDistinguishes_generatedStabilizerSet_iff_range]
  exact checkDistinguishes_range_iff_syndrome_ne_zero generators E
end QEC.Coding.PauliSymplectic
