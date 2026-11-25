-- Prove2me | solution 1 for PI.RhsWLim.W.dpsi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:42.878532+00:00
-- url     : https://prove2.me/submissions/0f4d55ff-21ec-4b31-9bf8-d3cec38b7f89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_mulVec_base

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
theorem _root_.solution (T' : ℝ) (q : TrE k) (i : Fin (2 * r + k + 1)) :
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) q i
      = (Real.sqrt T' : ℂ) * opGen k r q i (wI k r (Fin.last k)) := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, opGenL_apply, mvL_apply]
  exact mulVec_base T' _ i
end PI.RhsWLim.W
