-- Prove2me | solution 1 for PI.KLW.Pair.epsSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:44.392125+00:00
-- url     : https://prove2.me/submissions/f8ef5762-1cde-4c52-8861-3393fff05999

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_NO_eps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution : EpsSplit := by
  intro K _ _ c p hK hc hp hs k
  exact NO.eps c hc hK hp hs k
end PI.KLW.Pair
