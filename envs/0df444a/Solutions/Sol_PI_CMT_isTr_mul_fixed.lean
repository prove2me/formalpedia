-- Prove2me | solution 1 for PI.CMT.isTr_mul_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:12.19897+00:00
-- url     : https://prove2.me/submissions/b26b9cd5-c072-4d52-ad16-2d11abf8b5c8

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
theorem _root_.solution {b s : 𝓞 K} (hb : conj b = b) (hs : IsTr s) : IsTr (b * s) := by
  obtain ⟨x, rfl⟩ := hs
  exact ⟨b * x, by rw [map_mul, hb]; ring⟩
end PI.CMT
