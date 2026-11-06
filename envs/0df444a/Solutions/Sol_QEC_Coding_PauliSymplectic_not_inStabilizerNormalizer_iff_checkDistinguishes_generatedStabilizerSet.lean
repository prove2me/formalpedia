-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.not_inStabilizerNormalizer_iff_checkDistinguishes_generatedStabilizerSet
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:56:06.242371+00:00
-- url     : https://prove2.me/submissions/0a8ca414-a7c3-48b8-872b-4621b1631c47

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

theorem solution {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    ¬ InStabilizerNormalizer generators E ↔
      checkDistinguishes (generatedStabilizerSet generators) E := by
  solve | rfl | simp [PauliSymplectic, Binary, generatedStabilizerSet, InStabilizerNormalizer, checkDistinguishes] | simp_all [PauliSymplectic, Binary, generatedStabilizerSet, InStabilizerNormalizer, checkDistinguishes] | omega | norm_num
