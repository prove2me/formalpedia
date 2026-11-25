-- Prove2me | solution 1 for PI.RhsWLim.W.RI.avg_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:18.619472+00:00
-- url     : https://prove2.me/submissions/cb368d23-c542-4a28-96e3-6f8f7ccbd879

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Theorems.Thm_PI_RhsWLim_W_RI_avg_mul_mem

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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.RhsWLim.W.RI
theorem _root_.solution (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k
end PI.RhsWLim.W.RI
