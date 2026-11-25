-- Prove2me | solution 1 for PI.VolStabW.appr_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:10.869311+00:00
-- url     : https://prove2.me/submissions/99460080-acac-4c25-ba0f-0726a1a1fbaa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_exists_appr

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dif_pos h]
  exact h.choose_spec
end PI.VolStabW
