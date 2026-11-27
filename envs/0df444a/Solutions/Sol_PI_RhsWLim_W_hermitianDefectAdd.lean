-- Prove2me | solution 1 for PI.RhsWLim.W.hermitianDefectAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:17:17.38736+00:00
-- url     : https://prove2.me/submissions/b95e8357-57f6-41eb-9bf8-c23dc681271d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_DL_det
import Theorems.Thm_PI_RhsWLim_W_phiT_contDiffAt
import Theorems.Thm_PI_RhsWLim_W_phiT_strict

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
theorem _root_.solution : PhiDiff := by
  intro k r T' _ hT
  refine ⟨phiT_contDiffAt T' hT, ?_⟩
  rw [(phiT_strict (r := r) T' hT).hasFDerivAt.fderiv]
  exact DL_det T' hT
end PI.RhsWLim.W
