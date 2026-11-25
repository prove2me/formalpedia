-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq_zpow_sum_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:44.146354+00:00
-- url     : https://prove2.me/submissions/9e7f2a20-0557-4861-9002-21afa54375b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {M : Type*} [CommGroupWithZero M] {α : Type*}
    (s : Finset α) (f : α → ℤ) (a : M) (ha : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ ha]
end ReciprocityTheory.ChartRestriction.G.T0
