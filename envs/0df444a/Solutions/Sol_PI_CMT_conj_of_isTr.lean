-- Prove2me | solution 1 for PI.CMT.conj_of_isTr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:41.671516+00:00
-- url     : https://prove2.me/submissions/c7328c5a-8aca-437b-a1a0-363e752d1fab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_conj_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
namespace PI.CMT
theorem _root_.solution {s : 𝓞 K} (hs : IsTr s) : conj s = s := by
  obtain ⟨x, rfl⟩ := hs
  rw [map_add, conj_conj, add_comm]
end PI.CMT
