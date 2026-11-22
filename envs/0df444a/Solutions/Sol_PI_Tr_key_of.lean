-- Prove2me | solution 1 for PI.Tr.key_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:58.565283+00:00
-- url     : https://prove2.me/submissions/6eb4f13b-bab0-4ebd-9a9d-9c580d7089a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution (hL : KeyLarge) (hS : KeySmall) : PI.TransferenceKey := by
  intro E _ _ _ Λ _ _ lam u hlam hu
  rcases Nat.lt_or_ge (finrank ℝ E) 2 with h | h
  · exact hS E Λ lam u (by omega) hlam hu
  · exact hL E Λ lam u h hlam hu
end PI.Tr
