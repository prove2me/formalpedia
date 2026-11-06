-- Prove2me | solution 2 for QEC.Coding.PauliSymplectic.checkDistinguishes_range_iff_exists_syndromeBit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:09:10.815963+00:00
-- url     : https://prove2.me/submissions/b64ad476-45f8-4740-806d-3866ade83ae4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndromeBit_eq_one_iff_not_commutes

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
    checkDistinguishes (Set.range generators) E ↔
      ∃ j, stabilizerSyndromeBit (generators j) E = 1 := by
  constructor
  · rintro ⟨M, ⟨j, rfl⟩, hNotCommutes⟩
    exact ⟨j, (stabilizerSyndromeBit_eq_one_iff_not_commutes _ _).2 hNotCommutes⟩
  · rintro ⟨j, hOne⟩
    exact ⟨generators j, ⟨j, rfl⟩,
      (stabilizerSyndromeBit_eq_one_iff_not_commutes _ _).1 hOne⟩
end QEC.Coding.PauliSymplectic
