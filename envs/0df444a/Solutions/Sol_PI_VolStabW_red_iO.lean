-- Prove2me | solution 1 for PI.VolStabW.red_iO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:34.089928+00:00
-- url     : https://prove2.me/submissions/46358f9a-f8da-46ae-9f6b-3a1fd1e061df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_red_eq_mk_iff
import Theorems.Thm_PI_VolStabW_mem_O_iO

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
theorem _root_.solution (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := by
  rw [red_eq_mk_iff v (mem_O_iO v a) a]
  simp
end PI.VolStabW
