-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_mConeMap_weightedHomogeneousComponent_ec0138e761d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:55.979599+00:00
-- url     : https://prove2.me/submissions/08dc39ec-2c31-4529-b5cf-c0169202b9c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isWeightedHomogeneous_mConeMap_10701347c754

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    (f : MvPolynomial (Coord n) ℤ) (b : ι → ℕ) :
    Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) b f) =
      weightedHomogeneousComponent (tDeg ι) b (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by
  classical
  conv_rhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum]
  have hom : ∀ a, IsWeightedHomogeneous (tDeg ι)
      (Geo.mConeMap (ι := blockIdx n) (flatCone x) (weightedHomogeneousComponent (coordDeg n) a f)) a :=
    fun a ↦ isWeightedHomogeneous_mConeMap x (weightedHomogeneousComponent_isWeightedHomogeneous a f)
  rw [Finset.sum_eq_single b]
  · exact (IsWeightedHomogeneous.weightedHomogeneousComponent_same (hom b)).symm
  · intro a _ hab
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne b (hom a) (Ne.symm hab)
  · intro hb
    have h0 : weightedHomogeneousComponent (coordDeg n) b f = 0 := by
      by_contra h
      exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [h0, map_zero, map_zero]
end GroundTheory.Heights₂.Heights.OrbitCurve
