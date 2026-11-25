-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.supSt_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:41.219919+00:00
-- url     : https://prove2.me/submissions/2eb5f0fe-7a68-486c-bbb0-4ddd2d3e8449

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_sphProb_of_ne
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_sq_sphProb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a b : Fin (D + 1) → ℕ) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) =
      if a = b then (monoNormSq a : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have hz : ∀ z, starRingEnd ℂ (monoC a z) * monoC a z = ((‖monoC a z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      rw [Complex.conj_mul']
      push_cast
      ring
    simp_rw [hz]
    rw [integral_complex_ofReal, integral_mono_sq_sphProb]
  · exact integral_mono_sphProb_of_ne h
end ReciprocityTheory.GeometryOfNumbersTheory
