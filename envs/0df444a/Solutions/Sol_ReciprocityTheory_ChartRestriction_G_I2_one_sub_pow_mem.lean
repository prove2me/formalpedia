-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.one_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:14:42.38268+00:00
-- url     : https://prove2.me/submissions/ee27ac8b-3032-43cf-8edf-a8bda466d708

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCurveAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {A : Type*} [CommRing A] (h : A) (K : Ideal A) (hK : h - 1 ∈ K) (m : ℕ) :
    1 - h ^ m ∈ K := by
  rw [← Ideal.Quotient.eq]
  have h1 : Ideal.Quotient.mk K h = 1 := by
    rw [← map_one (Ideal.Quotient.mk K)]; exact Ideal.Quotient.eq.mpr hK
  simp [map_pow, h1]
end ReciprocityTheory.ChartRestriction.G.I2
