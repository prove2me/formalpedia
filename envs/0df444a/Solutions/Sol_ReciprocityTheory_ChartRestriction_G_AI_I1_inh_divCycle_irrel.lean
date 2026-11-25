-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_divCycle_irrel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:21.740943+00:00
-- url     : https://prove2.me/submissions/038b733e-1604-4a7a-816d-dba3d741e99a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
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
theorem _root_.solution (P : Ideal (MRingOver F ι)) (s : MRingOver F ι) (Q : Ideal (MRingOver F ι))
    [Q.IsPrime] (hQ : P ⊔ Ideal.span {s} = Q) (hrel : ¬ IsRelevant Q) : divCycle P s = 0 := by
  apply inh_divCycle_of_supp_empty
  ext W
  simp only [divSupp, hQ, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl; exact hrel
end ReciprocityTheory.ChartRestriction.G.AI.I1
