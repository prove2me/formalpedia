-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.nu_aSet_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:06.840679+00:00
-- url     : https://prove2.me/submissions/b7f1ac10-280b-433b-93b3-927c386de03b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_meas_chartF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_cont_zF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_zF_chart
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_src_null
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_wvol_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) (n : ℕ) :
    nuR k r z z' μW μW' μsec {x | ‖zF k r z z' x‖ ≤ n} < ⊤ := by
  have := hD.haarW.1
  have := hD.haarW'.1
  have hF := meas_chartF hD.sec
  have hA : MeasurableSet {x : Mt k r | ‖zF k r z z' x‖ ≤ n} :=
    (isClosed_le cont_zF.norm continuous_const).measurableSet
  rw [nuR, Measure.map_apply hF hA]
  have hsub : chartF k r z z' μsec ⁻¹' {x | ‖zF k r z z' x‖ ≤ n} ⊆
      (Metric.closedBall (0 : ℂ) n ×ˢ Set.univ) ∪ (goodS k r z z')ᶜ := by
    intro q hq
    by_cases hg : q ∈ goodS k r z z'
    · left
      refine ⟨?_, trivial⟩
      have hq' : ‖q.1‖ ≤ n := by
        rw [← zF_chart hD hg]
        exact hq
      exact mem_closedBall_zero_iff.2 hq'
    · exact Or.inr hg
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [src_null hD, add_zero, srcM, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod, hD.massW,
    hD.massW']
  exact ENNReal.mul_lt_top (wvol_lt (mul_pos hD.T_pos hD.T'_pos).le n)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
end PI.RhsWLim.W.ZetaZeros
