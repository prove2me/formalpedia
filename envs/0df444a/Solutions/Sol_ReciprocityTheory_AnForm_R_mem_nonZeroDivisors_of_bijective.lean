-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mem_nonZeroDivisors_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:57:09.076155+00:00
-- url     : https://prove2.me/submissions/f0b0f15f-f157-45fe-a3a6-8aaa821e8726

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * φ a = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hb.2 x
    have hz : z * a = 0 := hb.1 (by rw [map_mul, map_zero]; exact hx)
    rw [(mem_nonZeroDivisors_iff.mp ha).2 z hz, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩
end ReciprocityTheory.AnForm.R
