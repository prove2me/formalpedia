-- Prove2me | solution 1 for PI.VolStabW.red_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:36.526189+00:00
-- url     : https://prove2.me/submissions/a1fcff9e-c167-4b63-b59c-35942a678833

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_v_iO_lt_iff
import Theorems.Thm_PI_VolStabW_appr_spec

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff, iO, iO, map_sub, map_sub]
  have h0 := appr_spec v hx
  constructor
  · intro h
    have : x - iO v a = (x - iO v (appr v x)) + (iO v (appr v x) - iO v a) := by ring
    rw [this]; exact Valuation.map_add_lt _ h0 h
  · intro h
    have : iO v (appr v x) - iO v a = (x - iO v a) - (x - iO v (appr v x)) := by ring
    show Valued.v (iO v (appr v x) - iO v a) < 1
    rw [this]; exact Valuation.map_sub_lt _ h h0
end PI.VolStabW
