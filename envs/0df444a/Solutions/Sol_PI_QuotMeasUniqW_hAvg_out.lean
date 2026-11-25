-- Prove2me | solution 1 for PI.QuotMeasUniqW.hAvg_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:04.297975+00:00
-- url     : https://prove2.me/submissions/e9bf7b7d-07c1-4ea7-b852-219fe814ac8f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_hAvg_mul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
namespace PI.QuotMeasUniqW
private theorem exists_out_eq_mul {G : Type} [Group G] {H : Subgroup G} (g : G) :
    ∃ h : H, (g : G ⧸ H).out = g * (h : G) := by
  exact QuotientGroup.mk_out_eq_mul H g
end PI.QuotMeasUniqW
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    hAvg ν f ((g : G ⧸ H).out) = hAvg ν f g := by
  obtain ⟨h0, hh⟩ := exists_out_eq_mul (H := H) g
  rw [hh]
  exact hAvg_mul_mem ν f g h0
end PI.QuotMeasUniqW
