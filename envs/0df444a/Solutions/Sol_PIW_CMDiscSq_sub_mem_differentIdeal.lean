-- Prove2me | solution 1 for PIW.CMDiscSq.sub_mem_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:20.355806+00:00
-- url     : https://prove2.me/submissions/58b67206-75b8-4a10-974c-3699b8833864

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_SubMemDifferentIdeal
import Theorems.Thm_PIW_CMDiscSq_adjoin_eq_top_of_star_ne
import Theorems.Thm_PIW_CMDiscSq_minpoly_eq_of_star_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) (hne : θ - t ≠ 0) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 E) E
  have hx : star (algebraMap (𝓞 E) E θ) ≠ algebraMap (𝓞 E) E θ := by
    intro h
    apply hne
    rw [sub_eq_zero]
    apply hinj
    rw [ht, h]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ (adjoin_eq_top_of_star_ne hR hx)
  obtain ⟨s, n, hs, hn, hmin⟩ := minpoly_eq_of_star_ne hR hx
  have hAx : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hval : algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) =
      algebraMap (𝓞 E) E (θ - t) := by
    have h1 : aeval (algebraMap (𝓞 E) E θ) (derivative (minpoly F (algebraMap (𝓞 E) E θ))) =
        algebraMap (𝓞 E) E (aeval θ (derivative (minpoly (𝓞 F) θ))) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F E hAx, derivative_map,
        aeval_map_algebraMap, aeval_algebraMap_apply]
    rw [← h1, hmin, map_sub, ht]
    simp only [derivative_X_pow, derivative_mul, derivative_C, derivative_X, map_add, map_sub,
      map_mul, map_pow, aeval_X, aeval_C, hs, zero_mul, zero_add, mul_one, add_zero,
      Nat.cast_ofNat, map_ofNat]
    ring
  rw [hinj hval] at hmem
  exact hmem
end PIW.CMDiscSq
