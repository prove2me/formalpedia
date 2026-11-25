-- Prove2me | solution 1 for algValsFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:41.187707+00:00
-- url     : https://prove2.me/submissions/fb7df2a1-f8a3-4d71-8be9-605f41efe992

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AlgValsFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AlgValsFin
import Theorems.Thm_algebraic_values_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  algebraic_values_finite L
