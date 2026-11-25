-- Prove2me | solution 1 for PI.VolStabW.ev_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:52.119638+00:00
-- url     : https://prove2.me/submissions/464f1141-1210-4f19-b9f1-36a7e5c4f654

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_ev_int

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
theorem _root_.solution {x : F} (hx : x ≠ 0) : ∀ᶠ v in cofinite,
    Valued.v (algebraMap F (Fv F v) x) = 1 := by
  filter_upwards [ev_int x, ev_int x⁻¹] with w h1 h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap F (Fv F w) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; simpa using hx
  by_contra hne
  have hlt : Valued.v (algebraMap F (Fv F w) x) < 1 := lt_of_le_of_ne h1 hne
  exact absurd h2 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))
end PI.VolStabW
