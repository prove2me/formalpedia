-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:23.906676+00:00
-- url     : https://prove2.me/submissions/1fd1236c-d458-4e22-af53-4f71e151443e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {σ : Type*} (y : σ → Ω) {g : MvPolynomial σ S} {d : ℕ}
    (hg : g.IsHomogeneous d) : coneGen y g = Polynomial.C (aeval y g) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ i ∈ s.support, s i = d := by
    have := hg (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [coneGen, aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    map_prod, map_pow]
  rw [hdeg, mul_assoc]
end GroundTheory.Heights₂.Heights.Kleiman
