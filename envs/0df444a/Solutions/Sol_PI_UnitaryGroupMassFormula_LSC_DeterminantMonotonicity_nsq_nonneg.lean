-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.nsq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:03.257493+00:00
-- url     : https://prove2.me/submissions/a15c5056-b3cc-460b-8beb-506a879546fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
theorem _root_.solution {n : ℕ} (w : Fin n → ℂ) : 0 ≤ nsq w :=
  Finset.sum_nonneg fun _ _ => by positivity
end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
