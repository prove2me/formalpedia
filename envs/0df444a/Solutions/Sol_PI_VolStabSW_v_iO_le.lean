-- Prove2me | solution 1 for PI.VolStabSW.v_iO_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:03.894945+00:00
-- url     : https://prove2.me/submissions/dcea112b-6502-4808-836d-0a34dbf32bec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_vcoe

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
theorem _root_.solution (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  show Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) ≤ 1
  rw [vcoe]
  exact v.valuation_le_one a
end PI.VolStabSW
