-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:10.943224+00:00
-- url     : https://prove2.me/submissions/ee28ed75-ead4-4d4c-a6b5-b6352c587c9e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → MRingOver F ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_zero (F := F) (ι := ι) a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact isMultiHomog_add (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))
end ReciprocityTheory.ChartRestriction.G.AI.I1
