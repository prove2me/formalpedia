-- Prove2me | solution 1 for PI.VolStabW.lt_one_iff_le_expm1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:07:50.874084+00:00
-- url     : https://prove2.me/submissions/e0e0a2e3-ccd3-4039-ad87-820645514863

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes

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
theorem _root_.solution (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, g = WithZero.exp n := ⟨WithZero.log g, (WithZero.exp_log hg).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega
end PI.VolStabW
