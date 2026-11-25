-- Prove2me | solution 1 for PI.QuotMeasUniqW.lintegral_qLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:54.554408+00:00
-- url     : https://prove2.me/submissions/f7d4fad9-8566-4008-bfcf-fc159b81108e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_lintegral_qKer
import Theorems.Thm_PI_QuotMeasUniqW_measurable_qKer

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
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] (ρ : Measure (G ⧸ H)) {f : G → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂qLift ν ρ = ∫⁻ y, hAvg ν f y.out ∂ρ := by
  have hb : ∫⁻ x, f x ∂qLift ν ρ = ∫⁻ y, ∫⁻ x, f x ∂qKer ν y ∂ρ := by
    exact Measure.lintegral_bind (measurable_qKer ν).aemeasurable hf.aemeasurable
  rw [hb]
  exact lintegral_congr fun y => lintegral_qKer ν hf y
end PI.QuotMeasUniqW
