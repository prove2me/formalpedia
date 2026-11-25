-- Prove2me | solution 1 for PI.SqPairLocal.realUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:44.326076+00:00
-- url     : https://prove2.me/submissions/94dd8838-588e-4bd0-a290-a8654d91afed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer
import Theorems.Thm_PI_SqPairLocal_RU_exists_conjugation_fixed_uniformizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI.SqPairLocal
namespace PI.SqPairLocal
theorem _root_.solution : RealUnif := by
  intro E _ _ _ hE Q hQ hc
  exact RU.exists_conjugation_fixed_uniformizer hE Q hQ hc
end PI.SqPairLocal
