-- Prove2me | solution 1 for PI.RhsWLim.W.RI.rInvNu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:02.89362+00:00
-- url     : https://prove2.me/submissions/62a2c897-5d3f-455f-a7a6-8bc9121a9ba8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Theorems.Thm_PI_RhsWLim_W_RI_rhsW_rmul
import Theorems.Thm_PI_RhsWLim_W_RI_rmulM_cont
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_repr


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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution : RInvNu := by
  intro k r z z' μW μW' a a' μsec hd b hb
  have hm : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  have hi : Measurable (s.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hs
  have e1 := ZetaZeros.repr hd (s.indicator 1) hi
  have e2 := ZetaZeros.repr hd (fun x => s.indicator 1 (rmulM b x)) (hi.comp hm)
  have e3 := rhsW_rmul hd b hb (s.indicator 1) hi
  rw [lintegral_indicator_one hs] at e1
  have e4 : ∫⁻ x, s.indicator 1 (rmulM b x) ∂(nuR k r z z' μW μW' μsec) =
      nuR k r z z' μW μW' μsec (rmulM b ⁻¹' s) := by
    rw [← lintegral_indicator_one (hm hs)]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator, Pi.one_apply]
    rfl
  rw [← e4, ← e2, e3, e1]
end PI.RhsWLim.W.RI
