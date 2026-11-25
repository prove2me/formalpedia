-- Prove2me | solution 1 for PI.OrbShared.continuous_killCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:03.75095+00:00
-- url     : https://prove2.me/submissions/3f54afdc-333b-46fc-abbb-c85fdf15b4d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst

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
theorem _root_.solution [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _
end PI.OrbShared
