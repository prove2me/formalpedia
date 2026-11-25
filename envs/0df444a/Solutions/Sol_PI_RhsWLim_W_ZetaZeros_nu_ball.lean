-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.nu_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:49.70413+00:00
-- url     : https://prove2.me/submissions/cf6c8cca-7cc7-4fd0-b145-4969778e790d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_cont_zF
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_nu_aSet_lt
import Theorems.Thm_PI_RhsWLim_W_continuous_expChart


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
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) :
    ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → nuR k r z z' μW μW' μsec (bBall k r ρ) < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    ((((isCompact_closedBall (0 : lieE (UWb k r)) 1).image (continuous_expChart k r (UWb k r))).image
      cont_zF).isBounded)
  obtain ⟨n, hn⟩ := exists_nat_ge C
  refine ⟨1, one_pos, fun ρ hρ hρ1 => lt_of_le_of_lt (measure_mono ?_) (nu_aSet_lt hD n)⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (hC _ ⟨_, ⟨y, Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ1.le hy), rfl⟩, rfl⟩).trans hn
end PI.RhsWLim.W.ZetaZeros
