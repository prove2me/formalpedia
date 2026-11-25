-- Prove2me | solution 1 for PI.VolStabSW.red_iO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:34.12866+00:00
-- url     : https://prove2.me/submissions/798eeaa4-c0dd-4d0d-b1b7-9495bc0f4cdf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_red_eq_mk_iff
import Theorems.Thm_PI_VolStabSW_mem_O_iO

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
theorem _root_.solution (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := (red_eq_mk_iff v (mem_O_iO v a) a).mpr (by simp)
end PI.VolStabSW
