-- Prove2me | solution 1 for PI.RhsWLim.W.psiV_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:48.916857+00:00
-- url     : https://prove2.me/submissions/c908293b-8a58-40d5-a35e-547a80ba1b34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff

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
theorem _root_.solution (T' : ℝ) : ContDiffAt ℝ 1 (psiV k r T') 0 := by
  have h1 : ContDiffAt ℝ 1 (opGen k r) (0 : TrE k) := (opGenL k r).contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 1 (NormedSpace.exp : Mat k r → Mat k r) (opGen k r 0) :=
    (exp_analytic (𝕂 := ℝ) (opGen k r 0)).contDiffAt
  exact (mvL k r (opBase k r T')).contDiff.contDiffAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)
end PI.RhsWLim.W
