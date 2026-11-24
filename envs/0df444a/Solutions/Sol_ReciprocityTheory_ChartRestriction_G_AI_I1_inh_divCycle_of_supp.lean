-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_divCycle_of_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:45.251143+00:00
-- url     : https://prove2.me/submissions/82c3f06b-f50e-45de-8423-b6ad8febf162

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

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
theorem _root_.solution (P : Ideal (MRingOver F ι)) (s : MRingOver F ι) (Q : Ideal (MRingOver F ι))
    (hsupp : divSupp P s = {Q}) :
    divCycle P s = Finsupp.single Q (multAt (P ⊔ Ideal.span {s}) Q) := by
  classical
  ext W
  rw [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.single_apply, hsupp, Set.mem_singleton_iff]
  by_cases h : W = Q
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
end ReciprocityTheory.ChartRestriction.G.AI.I1
