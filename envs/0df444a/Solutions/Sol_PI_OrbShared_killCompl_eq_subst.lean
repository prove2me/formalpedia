-- Prove2me | solution 1 for PI.OrbShared.killCompl_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:04.279558+00:00
-- url     : https://prove2.me/submissions/7beee65b-0358-4bea-8eb2-4027b36e577e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst
import Theorems.Thm_PI_OrbShared_killCompl_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OrbShared
open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
variable {σ τ υ R : Type*} [CommRing R]
namespace PI.OrbShared
theorem _root_.solution (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  have := killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f
  rw [subst_self] at this
  exact this
end PI.OrbShared
