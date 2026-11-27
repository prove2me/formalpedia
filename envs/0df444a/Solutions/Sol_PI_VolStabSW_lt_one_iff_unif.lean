-- Prove2me | solution 1 for PI.VolStabSW.lt_one_iff_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:26:29.599493+00:00
-- url     : https://prove2.me/submissions/b8ae4ad0-a677-4037-a067-4769fff84dc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_vcoe
import Theorems.Thm_PI_VolStabSW_lt_one_iff_le_expm1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW
theorem _root_.solution (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hπ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
    have h := vcoe v (v.valuation_exists_uniformizer F).choose
    rw [(v.valuation_exists_uniformizer F).choose_spec] at h
    exact h
  rw [Valuation.map_mul, map_inv₀, hπ, lt_one_iff_le_expm1,
    inv_mul_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), mul_one]
end PI.VolStabSW
