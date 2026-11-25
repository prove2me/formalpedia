-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.integrable_of_continuous_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:33.206104+00:00
-- url     : https://prove2.me/submissions/5d066784-1a21-45db-87c5-4cd2870e0618

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {F : X → ℂ} (hF : Continuous F) : Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
end PI.UnitaryGroupMassFormula.GelfCpt
