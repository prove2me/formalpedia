-- Prove2me | solution 1 for PI.RhsWLim.W.psiV_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:14.024395+00:00
-- url     : https://prove2.me/submissions/34c354af-a0f3-4091-919c-ca81f7171b2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_opGen_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) : HasStrictFDerivAt (psiV k r T')
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) 0 := by
  have h1 : HasStrictFDerivAt (opGen k r) (opGenL k r) (0 : TrE k) := (opGenL k r).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) (1 : Mat k r →L[ℝ] Mat k r)
      (opGen k r 0) := by
    rw [opGen_zero]
    exact hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos ℝ (Mat k r))
  exact (mvL k r (opBase k r T')).hasStrictFDerivAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)
end PI.RhsWLim.W
