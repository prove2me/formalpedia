-- Prove2me | solution 2 for QEC.Coding.PauliSymplectic.syndromeSeparatedByCheckSet_range_iff_relative_syndrome_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:09:21.733186+00:00
-- url     : https://prove2.me/submissions/88bbd3b6-48ae-4a0b-9021-434ff51676c2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_range_iff_syndrome_ne_zero

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
    syndromeSeparatedByCheckSet (Set.range generators) E F ↔
      stabilizerSyndrome generators (binaryMul (binaryDagger E) F) ≠ 0 := by
  exact checkDistinguishes_range_iff_syndrome_ne_zero generators
    (binaryMul (binaryDagger E) F)
end QEC.Coding.PauliSymplectic
