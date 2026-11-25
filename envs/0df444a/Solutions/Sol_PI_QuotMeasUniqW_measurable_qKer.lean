-- Prove2me | solution 1 for PI.QuotMeasUniqW.measurable_qKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:52.262803+00:00
-- url     : https://prove2.me/submissions/b60fd4c7-4414-4e4d-8c70-912995464af7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_measurable_hAvg_out
import Theorems.Thm_PI_QuotMeasUniqW_lintegral_qKer

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
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] : Measurable (qKer (H := H) ν) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hi : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  have e : (fun y : G ⧸ H => qKer ν y s)
      = fun y : G ⧸ H => hAvg ν (s.indicator 1) y.out := by
    funext y
    rw [← lintegral_qKer ν hi y, lintegral_indicator_one hs]
  rw [e]
  exact measurable_hAvg_out ν hi
end PI.QuotMeasUniqW
