-- Prove2me | solution 1 for PI.RhsWLim.W.beta_re_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:13.000999+00:00
-- url     : https://prove2.me/submissions/23cb791c-6926-4c5f-92e6-1c70844ae581

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
import Theorems.Thm_PI_RhsWLim_W_DL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.RhsWLim.W.DL_apply

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (T' : ℝ) (q : TrE k) (a : Fin k) :
    (Real.sqrt T' : ℂ) * opBeta k q a =
      ((Real.sqrt T' / Real.sqrt 2 * q (some (a, false)) : ℝ) : ℂ)
        + ((Real.sqrt T' / Real.sqrt 2 * q (some (a, true)) : ℝ) : ℂ) * Complex.I := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  simp only [opBeta]
  push_cast
  field_simp
end PI.RhsWLim.W
