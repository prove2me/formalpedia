-- Prove2me | solution 1 for PI.WAU.maximal_compact_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:23.700373+00:00
-- url     : https://prove2.me/submissions/ed1203a7-35d6-479f-a3e0-3d39b9fa6321

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
import Theorems.Thm_PI_WAU_Cpt_isCompact_Kset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct Matrix
namespace PI.WAU
theorem _root_.solution : KCompact := fun I => Cpt.isCompact_Kset I
end PI.WAU
