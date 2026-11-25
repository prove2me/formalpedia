-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_opBeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:15.743814+00:00
-- url     : https://prove2.me/submissions/038019c4-7523-45aa-a401-edc285fa8cbd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (a : Fin k) : Continuous (fun q : TrE k => opBeta k q a) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  unfold opBeta
  exact ((hq _).add ((hq _).mul continuous_const)).div_const _
end PI.RhsWLim.W
