-- Prove2me | solution 1 for PI.QuotMeasUniqW.measurable_hAvg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:26.726155+00:00
-- url     : https://prove2.me/submissions/06bfa980-42d2-44d1-8290-862485851ba1

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
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) : Measurable (hAvg ν f) := by
  unfold hAvg
  have hm : Measurable (fun p : G × H => f (p.1 * (p.2 : G))) :=
    hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))
  exact hm.lintegral_prod_right'
end PI.QuotMeasUniqW
