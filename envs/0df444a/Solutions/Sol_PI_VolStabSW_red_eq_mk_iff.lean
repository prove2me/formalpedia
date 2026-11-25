-- Prove2me | solution 1 for PI.VolStabSW.red_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:19.086009+00:00
-- url     : https://prove2.me/submissions/473af978-8e83-4301-831f-40571f2bf6ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_v_iO_lt_iff
import Theorems.Thm_PI_VolStabSW_appr_spec

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
theorem _root_.solution {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff]
  have h1 := appr_spec v hx
  have e1 : iO v (appr v x - a) = (x - iO v a) + -(x - iO v (appr v x)) := by
    simp only [iO, map_sub]
    ring
  have e2 : x - iO v a = (x - iO v (appr v x)) + iO v (appr v x - a) := by
    simp only [iO, map_sub]
    ring
  constructor
  · intro h
    rw [e2]
    exact Valuation.map_add_lt _ h1 h
  · intro h
    rw [e1]
    refine Valuation.map_add_lt _ h ?_
    rw [Valuation.map_neg]
    exact h1
end PI.VolStabSW
