-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.exists_monomial_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:41.466194+00:00
-- url     : https://prove2.me/submissions/f4b0526d-9b05-4418-8a1f-8283a5c60fc9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_coordProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_coordProd_not_mem

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
theorem _root_.solution {W : Ideal (MRingOver F ι)} (hW : W.IsPrime) (hr : IsRelevant W)
    (d : K → ℕ) : ∃ f : MRingOver F ι, IsMultiHomog f d ∧ f ∉ W :=
  ⟨_, isMultiHomog_coordProd (fun k => (hr k).choose) d,
    coordProd_not_mem hW _ (fun k => (hr k).choose_spec) d⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
