-- Prove2me | solution 1 for PI.VolStabW.red_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:14:21.816239+00:00
-- url     : https://prove2.me/submissions/ca62ae9c-10db-44ba-9100-99a6ea89e972

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabW_v_iO_le
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
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have e : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) := by
    rw [map_mul]; rfl
  rw [e, red_eq_mk_iff v (mul_mem hx hy)]
  have : x * y - iO v (appr v x * appr v y) =
      x * (y - iO v (appr v y)) + iO v (appr v y) * (x - iO v (appr v x)) := by
    simp only [iO, map_mul]; ring
  rw [this]
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    calc Valued.v x * Valued.v (y - iO v (appr v y)) ≤ 1 * Valued.v (y - iO v (appr v y)) :=
          mul_le_mul_left hx1 _
      _ < 1 := by rw [one_mul]; exact appr_spec v hy
  · rw [map_mul]
    calc Valued.v (iO v (appr v y)) * Valued.v (x - iO v (appr v x)) ≤
          1 * Valued.v (x - iO v (appr v x)) := mul_le_mul_left (v_iO_le v _) _
      _ < 1 := by rw [one_mul]; exact appr_spec v hx
end PI.VolStabW
