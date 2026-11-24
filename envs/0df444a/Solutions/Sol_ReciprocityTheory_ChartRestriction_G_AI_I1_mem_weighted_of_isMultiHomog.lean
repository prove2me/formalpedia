-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mem_weighted_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:00.453823+00:00
-- url     : https://prove2.me/submissions/420b57fb-f53f-4944-8a54-879a32bc7914

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt

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
variable [DecidableEq K]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {f : MRingOver F ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : f ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) a := by
  rw [mem_weightedHomogeneousSubmodule]
  intro m hm
  rw [weight_mw]
  unfold IsMultiHomog at hf
  have h := hf m (by simpa [MvPolynomial.mem_support_iff] using hm)
  first
    | exact h
    | exact funext h
    | simpa [funext_iff] using h
end ReciprocityTheory.ChartRestriction.G.AI.I1
