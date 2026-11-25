-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:52.612516+00:00
-- url     : https://prove2.me/submissions/03d665c1-0990-40c6-b101-0b94d5572392

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ
omit [IsDomain O] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V) (F : MvPolynomial (Coord n) ℤ) :
    betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) F
  have hsum : F = ∑ e ∈ hfin.toFinset, weightedHomogeneousComponent (coordDeg n) e F := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) F, finsum_eq_sum _ hfin]
  have hcone : γ F = ∑ e ∈ hfin.toFinset,
      C (ε (weightedHomogeneousComponent (coordDeg n) e F)) * ∏ k, X k ^ e k := by
    conv_lhs => rw [hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun e _ ↦ hγ (weightedHomogeneousComponent_isWeightedHomogeneous e F)
  rw [betaB, RingHom.comp_apply,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (locB ι (V.map ε)) (fibO ι (V.map ε)), hcone]
  constructor
  · intro h
    rw [hsum]
    refine V.sum_mem fun e he ↦ ?_
    have h' := MvPolynomial.mem_map_C_iff.mp h (Finsupp.equivFunOnFinite.symm e)
    rw [coeff_sum_C_mul_prod_X_pow _ _ he] at h'
    exact hD (weightedHomogeneousComponent_isWeightedHomogeneous e F) h'
  · intro h
    exact Ideal.sum_mem _ fun e _ ↦ Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hV F h e)))
end GroundTheory.Heights₂.Heights.OrbitChartMult
