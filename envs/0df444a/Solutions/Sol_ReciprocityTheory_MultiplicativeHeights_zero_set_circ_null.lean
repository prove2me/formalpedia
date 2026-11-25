-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.zero_set_circ_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:01.198652+00:00
-- url     : https://prove2.me/submissions/ff25382d-bf5e-4a35-bf4f-219baa086b84

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_circPt_injOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) (hp : p ≠ 0) :
    volume.restrict (Set.Ioc (0 : ℝ) 1) {t | p.eval (circPt t) = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  apply Set.Finite.measure_zero _ volume
  apply Set.Finite.of_finite_image (f := circPt) _ (circPt_injOn.mono fun _ h => h.2)
  apply p.roots.finite_toSet.subset
  rintro _ ⟨t, ⟨ht, _⟩, rfl⟩
  simpa [mem_roots hp] using ht
end ReciprocityTheory.MultiplicativeHeights
