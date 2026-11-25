-- Prove2me | solution 1 for algebraic_values_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:49.506889+00:00
-- url     : https://prove2.me/submissions/b2c4a37c-f87b-4e90-8824-48e8e93a295f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AlgValsFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AlgValsFin
import Theorems.Thm_PI_AlgValsFin_W_algValsFin_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  PI.AlgValsFin.W.algValsFin_main L
