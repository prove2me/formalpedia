-- Prove2me | solution 1 for PI.VolStabSW.red_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:12.404828+00:00
-- url     : https://prove2.me/submissions/25d3d134-699a-4fab-85d3-98444d450fc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_red_add
import Theorems.Thm_PI_VolStabSW_red_zero

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : red v (-x) = -red v x := by
  have h := red_add v hx (neg_mem hx)
  rw [add_neg_cancel, red_zero] at h
  linear_combination (-1 : 𝓞 F ⧸ v.asIdeal) * h
end PI.VolStabSW
