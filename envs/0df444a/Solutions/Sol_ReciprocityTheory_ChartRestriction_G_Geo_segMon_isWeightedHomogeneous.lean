-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.segMon_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:34.527416+00:00
-- url     : https://prove2.me/submissions/96e4ba88-fd8c-4bb7-b6a1-41ada7df3faf

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
theorem _root_.solution (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (segMon i) oneK := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℚ)) (fun k => blkWt (ι := ι) ⟨k, i k⟩)
    (fun k _ => isWeightedHomogeneous_X ℚ _ _)
  have e : (∑ k ∈ Finset.univ, blkWt (ι := ι) ⟨k, i k⟩) = oneK := by
    ext k
    rw [Finsupp.finset_sum_apply]
    simp only [blkWt, oneK, Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
    simp
  rw [e] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.Geo
