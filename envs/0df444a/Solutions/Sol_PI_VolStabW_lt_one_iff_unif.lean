-- Prove2me | solution 1 for PI.VolStabW.lt_one_iff_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:50.286398+00:00
-- url     : https://prove2.me/submissions/141da857-2218-45f6-8718-e3a585a33ab1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_lt_one_iff_le_expm1
import Theorems.Thm_PI_VolStabW_unifV_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW
theorem _root_.solution (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hπ := unifV_val v
  rw [map_mul, map_inv₀, hπ, lt_one_iff_le_expm1]
  constructor
  · intro h
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1) :=
          mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · intro h
    have h2 := mul_le_mul' h (le_refl (WithZero.exp (-1 : ℤ)))
    rwa [mul_comm, ← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul, one_mul] at h2
end PI.VolStabW
