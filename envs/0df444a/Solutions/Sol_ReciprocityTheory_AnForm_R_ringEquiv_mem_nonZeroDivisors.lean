-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringEquiv_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:23.783251+00:00
-- url     : https://prove2.me/submissions/e75ad4a0-4bf9-41bc-a06e-2bcc5d043081

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {a : A}
    (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right] at ha ⊢
  intro x hx
  have : e.symm x * a = 0 := by
    apply e.injective; rw [map_mul, e.apply_symm_apply, hx, map_zero]
  simpa using congrArg e (ha _ this)
end ReciprocityTheory.AnForm.R
