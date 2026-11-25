-- Prove2me | solution 1 for PI.CMT.isTr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:45.07384+00:00
-- url     : https://prove2.me/submissions/33e19ce0-4e98-4f98-8caa-acfd7f492561

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem

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
theorem _root_.solution {s t : 𝓞 K} (hs : IsTr s) (ht : IsTr t) : IsTr (s + t) := by
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, rfl⟩ := ht
  exact ⟨x + y, by rw [map_add]; ring⟩
end PI.CMT
