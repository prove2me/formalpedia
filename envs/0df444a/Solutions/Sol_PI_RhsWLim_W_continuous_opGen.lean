-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_opGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:17.216421+00:00
-- url     : https://prove2.me/submissions/2fa64417-8e0d-46b2-8a95-f3d9c6c94731

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Theorems.Thm_PI_RhsWLim_W_continuous_opBeta

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
theorem _root_.solution (k r : ℕ) : Continuous (opGen k r : TrE k → Mat k r) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold opGen
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_opBeta k _
    | exact (continuous_opBeta k _).star
    | exact (hq none).mul continuous_const
end PI.RhsWLim.W
