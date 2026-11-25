-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_divCycle_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:06.75938+00:00
-- url     : https://prove2.me/submissions/3fe01b31-c56b-4e93-8f07-36d134519ba7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_minimalPrimes_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_of_supp_empty

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (P : Ideal (MRingOver F ι)) : divCycle P 1 = 0 := by
  apply inh_divCycle_of_supp_empty
  ext W
  simp [divSupp, Ideal.span_singleton_one, inh_minimalPrimes_top]
end ReciprocityTheory.ChartRestriction.G.AI.I1
