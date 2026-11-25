-- Prove2me | solution 1 for PI.KLW.pairOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:22.255681+00:00
-- url     : https://prove2.me/submissions/5c12d66c-c58e-43b9-a8e7-7cdd61155e84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_Pair_pairOne_of
import Theorems.Thm_PI_KLW_Pair_epsSplit

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
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution : PairOne := Pair.pairOne_of Pair.epsSplit
end PI.KLW
