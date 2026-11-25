-- Prove2me | solution 1 for PI.QuotMeasUniqW.measurable_smul_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:32.130538+00:00
-- url     : https://prove2.me/submissions/d54d3cc4-eef2-4e7a-88de-35632b1ff781

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (g : G) :
    Measurable (fun y : G ⧸ H => g • y) := by
  refine QuotientGroup.measurable_from_quotient.2 ?_
  exact QuotientGroup.measurable_coe.comp (measurable_const_mul g)
end PI.QuotMeasUniqW
