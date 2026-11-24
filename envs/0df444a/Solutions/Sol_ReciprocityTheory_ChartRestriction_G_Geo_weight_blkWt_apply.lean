-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.weight_blkWt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:12.152899+00:00
-- url     : https://prove2.me/submissions/ba62244f-7684-4a83-a6c0-5c9ae2e5b834

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkWt (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply,
    Fintype.sum_sigma]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [blkWt, Finsupp.single_apply, hk']
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [blkWt]
end ReciprocityTheory.ChartRestriction.G.Geo
