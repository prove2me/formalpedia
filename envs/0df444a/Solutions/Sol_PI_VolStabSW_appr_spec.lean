-- Prove2me | solution 1 for PI.VolStabSW.appr_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:33.280966+00:00
-- url     : https://prove2.me/submissions/9b6c6349-b31a-4fe8-8cc4-304b76990402

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_exists_appr

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dif_pos h]
  exact h.choose_spec
end PI.VolStabSW
