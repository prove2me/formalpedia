-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:43.440132+00:00
-- url     : https://prove2.me/submissions/9c949281-6773-4995-bfe1-060aa8058921

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_locQuot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_pow

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
variable {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [IsDomain R] (x : MRingOver R ι) (hx : x ≠ 0) [hW : (Ideal.span {x}).IsPrime]
    (m : ℕ) : multAt (Ideal.span {x ^ m}) (Ideal.span {x}) = m := by
  rw [multAt, dif_pos hW, inh_length_locQuot, inh_length_pow x hx]
  simp
end ReciprocityTheory.ChartRestriction.G.AI.I1
