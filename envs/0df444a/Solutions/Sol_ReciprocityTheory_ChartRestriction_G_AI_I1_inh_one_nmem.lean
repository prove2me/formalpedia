-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_one_nmem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:34.944323+00:00
-- url     : https://prove2.me/submissions/58a16937-0c95-4cd7-b130-f1e1942f79ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq (Σ k, ι k)]
  {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (S : Finset (Σ k, ι k)) : (1 : MRingOver F ι) ∉ inhV F S :=
  fun h => (inhV_isPrime F S).ne_top ((Ideal.eq_top_iff_one _).mpr h)
end ReciprocityTheory.ChartRestriction.G.AI.I1
