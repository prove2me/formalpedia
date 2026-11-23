-- Prove2me | solution 1 for PI.QuotMeasUniqW.lintegral_qKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.830152+00:00
-- url     : https://prove2.me/submissions/0a00092f-0aee-45b7-b2a3-f5d55f0b678d

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
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (ν : Measure H) {f : G → ℝ≥0∞}
    (hf : Measurable f) (y : G ⧸ H) : ∫⁻ x, f x ∂qKer ν y = hAvg ν f y.out := by
  unfold qKer hAvg
  exact lintegral_map hf ((measurable_const_mul _).comp measurable_subtype_coe)
end PI.QuotMeasUniqW
