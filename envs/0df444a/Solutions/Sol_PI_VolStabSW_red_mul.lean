-- Prove2me | solution 1 for PI.VolStabSW.red_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:51.252801+00:00
-- url     : https://prove2.me/submissions/bd04d92c-b9e3-4880-b591-4ad8fa0f72d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensCntRes
import Theorems.Thm_PI_VolStabSW_v_iO_le
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
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have hxy : x * y ∈ v.adicCompletionIntegers F := mul_mem hx hy
  rw [show red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) by simp only [red, map_mul]]
  rw [red_eq_mk_iff v hxy]
  have e : x * y - iO v (appr v x * appr v y) =
      (x - iO v (appr v x)) * y + iO v (appr v x) * (y - iO v (appr v y)) := by
    simp only [iO, map_mul]
    ring
  rw [e]
  have hy1 : Valued.v y ≤ 1 := hy
  apply Valuation.map_add_lt
  · rw [Valuation.map_mul]
    calc _ ≤ Valued.v (x - iO v (appr v x)) * 1 := by gcongr
      _ < 1 := by
        rw [mul_one]
        exact appr_spec v hx
  · rw [Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (y - iO v (appr v y)) := by
          have h2 := v_iO_le v (appr v x)
          gcongr
      _ < 1 := by
        rw [one_mul]
        exact appr_spec v hy
end PI.VolStabSW
