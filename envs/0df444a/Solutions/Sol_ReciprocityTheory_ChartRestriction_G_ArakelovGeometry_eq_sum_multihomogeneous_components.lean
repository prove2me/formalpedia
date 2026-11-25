-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_sum_multihomogeneous_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:32.506976+00:00
-- url     : https://prove2.me/submissions/3f958b6e-1d77-4f44-a5e2-a32c2f0aeb9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (r : MRing ι) :
    r = ∑ b ∈ r.support.image i2bdeg, i2comp b r := by
  classical
  ext m
  rw [coeff_sum]
  simp_rw [coeff_i2comp]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
