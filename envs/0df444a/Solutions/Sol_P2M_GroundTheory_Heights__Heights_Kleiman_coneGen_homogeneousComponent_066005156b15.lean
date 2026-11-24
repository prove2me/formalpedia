-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:56.201799+00:00
-- url     : https://prove2.me/submissions/7aff1637-9b23-4c4b-ac13-0ce508f22ad5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5

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
theorem _root_.solution {σ : Type*} (y : σ → Ω) {g : MvPolynomial σ S}
    (hg : coneGen y g = 0) (d : ℕ) : coneGen y (homogeneousComponent d g) = 0 := by
  classical
  rw [coneGen_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g)]
  by_cases hd : d < g.totalDegree + 1
  · have hsum : coneGen y g = ∑ i ∈ Finset.range (g.totalDegree + 1),
        Polynomial.C (aeval y (homogeneousComponent i g)) * Polynomial.X ^ i := by
      conv_lhs => rw [← sum_homogeneousComponent g]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ =>
        coneGen_of_isHomogeneous y (homogeneousComponent_isHomogeneous i g)
    have hc := congrArg (fun p => Polynomial.coeff p d) hsum
    simp only [hg, Polynomial.coeff_zero, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Finset.sum_ite_eq, Finset.mem_range, hd, if_true] at hc
    rw [← hc, map_zero, zero_mul]
  · rw [homogeneousComponent_eq_zero d g (by omega), map_zero, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.Kleiman
