-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:09.937585+00:00
-- url     : https://prove2.me/submissions/810f5724-4627-4512-9d08-ed69d358f346

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {ι : Type*} (w : AddValuation F (WithTop ℤ)) (S : Finset ι) (f : ι → F)
    (e : ι → ℤ) (h : ∀ i ∈ S, w (f i) = e i) :
    w (∏ i ∈ S, f i) = ((∑ i ∈ S, e i : ℤ) : WithTop ℤ) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one, WithTop.coe_zero]
  · intro j S hj ih h
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact wa_mul w (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end ReciprocityTheory.ChartRestriction.G.T0
