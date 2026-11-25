-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_hq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:10.973048+00:00
-- url     : https://prove2.me/submissions/f079801a-f2a4-408b-8ccb-f0edbed42b62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH

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
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (T' : ℝ) : Continuous (fun p : (Fin k → ℂ) × ℝ => hq k T' p.1 p.2) := by
  unfold hq
  refine continuous_fst.prodMk ?_
  refine (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    ((continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp
      ((continuous_apply i).comp continuous_fst)).add continuous_const))).mul ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end PI.RhsWLim.W
