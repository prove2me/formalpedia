-- Prove2me | solution 1 for PI.QuotMeasUniqW.hAvg_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:13.565031+00:00
-- url     : https://prove2.me/submissions/bc4e6e94-d4bf-4ea7-863b-5c029ef9bf7e

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
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (h0 : H) :
    hAvg ν f (g * h0) = hAvg ν f g := by
  have key := lintegral_mul_left_eq_self (μ := ν) (fun x : H => f (g * (x : G))) h0
  simp only [hAvg, Subgroup.coe_mul, mul_assoc] at key ⊢
  exact key
end PI.QuotMeasUniqW
