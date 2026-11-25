-- Prove2me | solution 1 for PI.VolStabW.red_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:28.429798+00:00
-- url     : https://prove2.me/submissions/69f7c9b7-11b5-4b5a-9deb-2f35bf4b53df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_appr_spec
import Theorems.Thm_PI_VolStabW_red_eq_mk_iff

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
theorem _root_.solution {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have e : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) := by
    rw [map_add]; rfl
  rw [e, red_eq_mk_iff v (add_mem hx hy)]
  have : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]; ring
  rw [this]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)
end PI.VolStabW
