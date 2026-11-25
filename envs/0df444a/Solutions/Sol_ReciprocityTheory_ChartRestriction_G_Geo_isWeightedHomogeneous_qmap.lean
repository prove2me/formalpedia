-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_qmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:44.918928+00:00
-- url     : https://prove2.me/submissions/dd3c9f78-09c3-41be-aedc-ab7308458169

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkWt_apply

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
theorem _root_.solution (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (qmap f) (Finsupp.equivFunOnFinite.symm a) := by
  intro d hd
  have hd' : d ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hd
    simp [qmap, MvPolynomial.coeff_map, h]
  ext k
  rw [weight_blkWt_apply, hf d hd' k]
  simp
end ReciprocityTheory.ChartRestriction.G.Geo
