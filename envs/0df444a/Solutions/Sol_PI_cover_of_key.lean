-- Prove2me | solution 1 for PI.cover_of_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:37.616848+00:00
-- url     : https://prove2.me/submissions/0d3d338a-3065-4c79-9b70-1642fb717321

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open PI
namespace PI
theorem _root_.solution (h : TransferenceKey) : TransferenceCover := by
  intro E _ _ _ Λ _ _ lam hlam hmin x
  refine h E Λ lam x hlam ?_
  intro y hy hlt
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0]⟩
  · exact absurd (hmin y hy0 hy) (not_le.mpr hlt)
end PI
