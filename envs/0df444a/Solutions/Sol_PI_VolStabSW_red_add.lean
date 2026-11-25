-- Prove2me | solution 1 for PI.VolStabSW.red_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:39.962895+00:00
-- url     : https://prove2.me/submissions/5a5db530-114b-44fe-9ad9-2e05113e8e5f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_appr_spec
import Theorems.Thm_PI_VolStabSW_red_eq_mk_iff

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
theorem _root_.solution {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have hxy : x + y ∈ v.adicCompletionIntegers F := add_mem hx hy
  rw [show red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) by simp only [red, map_add]]
  rw [red_eq_mk_iff v hxy]
  have e : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]
    ring
  rw [e]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)
end PI.VolStabSW
