-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_of_mem_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:01.203807+00:00
-- url     : https://prove2.me/submissions/e6d32499-3b56-468d-96f0-b593e6c2fe4b

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
    (hf : f ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) a) : IsMultiHomog f a := by
  unfold IsMultiHomog
  intro m hm
  rw [mem_weightedHomogeneousSubmodule] at hf
  have h := hf (by simpa [MvPolynomial.mem_support_iff] using hm)
  rw [weight_mw] at h
  first
    | exact h
    | exact congrFun h
    | simpa [funext_iff] using h
end ReciprocityTheory.ChartRestriction.G.AI.I1
