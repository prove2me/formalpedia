-- Prove2me | solution 1 for PI.SwSandwichOfWork.chartFwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:11.460726+00:00
-- url     : https://prove2.me/submissions/8948e63c-a6cf-412b-ae90-9d96f9f5d28f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
import Theorems.Thm_PI_SwSandwichOfWork_Chart_core

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
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : ChartFwdOf := by
  unfold ChartFwdOf ChartFwd
  intro hN hLog hW hBC hPF hPD hLW hEN hLI k r η hη
  obtain ⟨F, -, -, hFη⟩ := Chart_core hN hLog hW hBC hPF hPD hLW hEN hLI k r
  obtain ⟨δ, hδ, hδ'⟩ := hFη η hη
  refine ⟨δ, hδ, fun v hv hvn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hδ' v hv hvn
  refine ⟨F v, h1, h2, ?_⟩
  have h4 := norm_add_le (F v - Lm k r v) (Lm k r v)
  rw [sub_add_cancel] at h4
  nlinarith [h3, h4]
end PI.SwSandwichOfWork
