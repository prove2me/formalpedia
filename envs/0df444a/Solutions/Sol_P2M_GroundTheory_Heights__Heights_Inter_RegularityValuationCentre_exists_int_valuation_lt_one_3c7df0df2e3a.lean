-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_exists_int_valuation_lt_one_3c7df0df2e3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:07.230722+00:00
-- url     : https://prove2.me/submissions/e33d05b2-9a1c-40ae-94e5-e590634ecb6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityValuationCentre
theorem _root_.solution {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn
end RegularityValuationCentre
end GroundTheory.Heights₂.Heights.Inter
