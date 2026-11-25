-- Prove2me | solution 1 for PI.OrbShared.killCompl_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:22.517796+00:00
-- url     : https://prove2.me/submissions/ca2ae747-7601-463e-bd0f-5a38cd00d5d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst
import Theorems.Thm_PI_OrbShared_hasSubst_killCompl
import Theorems.Thm_PI_OrbShared_continuous_killCompl

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
theorem _root_.solution (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]
end PI.OrbShared
