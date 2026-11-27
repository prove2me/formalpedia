-- Prove2me | solution 1 for PI.OrbShared.ExpSum.rename_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:02.577438+00:00
-- url     : https://prove2.me/submissions/7695f8d6-c3c0-474e-b625-52a3f7e19aa7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_subst_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
variable {τ υ : Type*}
namespace PI.OrbShared.ExpSum
theorem _root_.solution (e : τ → υ) [Filter.TendstoCofinite e] (f : MvPowerSeries τ K) (hf : constantCoeff f = 0) :
    rename e (eS f) = eS (rename e f) := by
  rw [rename_eq_subst, rename_eq_subst]
  exact subst_eS (HasSubst.X_comp e) f hf
end PI.OrbShared.ExpSum
