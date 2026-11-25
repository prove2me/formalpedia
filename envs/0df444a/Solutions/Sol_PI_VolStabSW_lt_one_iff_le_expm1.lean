-- Prove2me | solution 1 for PI.VolStabSW.lt_one_iff_le_expm1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:09.349296+00:00
-- url     : https://prove2.me/submissions/20395225-121e-4c77-8453-aa62985d973a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes

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
theorem _root_.solution (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · constructor
    · intro _
      exact zero_le'
    · intro _
      exact zero_lt_one
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega
end PI.VolStabSW
