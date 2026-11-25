-- Prove2me | solution 1 for PI.OrbShared.ExpSum.eS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:13.424169+00:00
-- url     : https://prove2.me/submissions/0e3c57d5-ac18-4578-b209-6de2667b7c37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_eS_X_add_X
import Theorems.Thm_PI_OrbShared_ExpSum_subst_psubst

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
theorem _root_.solution (f g : MvPowerSeries τ K) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    eS (f + g) = eS f * eS g := by
  let b : Fin 2 → MvPowerSeries τ K := ![f, g]
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i <;> simp [b, hf, hg]
  have h1 : subst b (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) = eS (f + g) := by
    rw [subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_add hb, subst_X hb,
      subst_X hb]
    rfl
  have h2 : subst b (eS (X 0 : MvPowerSeries (Fin 2) K) * eS (X 1)) = eS f * eS g := by
    rw [subst_mul hb, subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_X hb, subst_X hb]
    rfl
  rw [← h1, eS_X_add_X, h2]
end PI.OrbShared.ExpSum
