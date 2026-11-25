-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:24.843112+00:00
-- url     : https://prove2.me/submissions/82a484d6-ddbf-4f51-b459-40503a3bd390

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
theorem _root_.solution [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    have hX : ∀ p : Σ k, ι k, IsWeightedHomogeneous (tWeight k)
        (RegularityFunctionFieldNumber.cS E ∅ p.1 * MvPolynomial.C (ψ (X p))) (tWeight k p.1) := by
      intro p
      simp only [RegularityFunctionFieldNumber.cS, Finset.notMem_empty, if_false]
      rw [mul_comm]
      exact (isWeightedHomogeneous_X E (tWeight k) p.1).C_mul _
    have hh : IsWeightedHomogeneous (tWeight k) (RegularityFunctionFieldNumber.specMap ψ ∅ (monomial m c))
        (Finsupp.weight (blockWeight k) m) := by
      rw [RegularityFunctionFieldNumber.specMap, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
        show algebraMap ℤ (MvPolynomial K E) c = MvPolynomial.C (c : E) by simp]
      exact (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hX p).pow (m p)).C_mul _
    have hm : IsWeightedHomogeneous (blockWeight k) (monomial m c) (Finsupp.weight (blockWeight k) m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : d = Finsupp.weight (blockWeight k) m
    · rw [h, hm.weightedHomogeneousComponent_same, hh.weightedHomogeneousComponent_same]
    · rw [hm.weightedHomogeneousComponent_ne d h, hh.weightedHomogeneousComponent_ne d h, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add (RegularityFunctionFieldNumber.specMap ψ ∅) p q]
    exact ((weightedHomogeneousComponent (R := E) (tWeight k) d).map_add _ _).symm
end GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
