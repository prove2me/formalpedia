-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_divCycle_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:46.384807+00:00
-- url     : https://prove2.me/submissions/577021de-4758-4e5c-b9f3-c61f26adc15b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_multAt_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_divCycle_of_supp

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
    [Q.IsPrime] (hQ : P ⊔ Ideal.span {s} = Q) (hrel : IsRelevant Q) :
    divCycle P s = Finsupp.single Q 1 := by
  rw [inh_divCycle_of_supp P s Q, hQ, inh_multAt_self]
  ext W
  simp only [divSupp, hQ, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hrel⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
