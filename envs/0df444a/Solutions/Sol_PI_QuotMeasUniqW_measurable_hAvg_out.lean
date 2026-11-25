-- Prove2me | solution 1 for PI.QuotMeasUniqW.measurable_hAvg_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:06.794947+00:00
-- url     : https://prove2.me/submissions/d1df442f-5a54-42e1-9bc9-a4f4ef782265

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_measurable_hAvg
import Theorems.Thm_PI_QuotMeasUniqW_hAvg_out

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
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun y : G ⧸ H => hAvg ν f y.out) := by
  refine QuotientGroup.measurable_from_quotient.2 ?_
  convert measurable_hAvg ν hf using 1
  funext g
  exact hAvg_out ν f g
end PI.QuotMeasUniqW
