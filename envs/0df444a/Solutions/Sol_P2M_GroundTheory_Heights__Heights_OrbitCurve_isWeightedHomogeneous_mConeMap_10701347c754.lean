-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_isWeightedHomogeneous_mConeMap_10701347c754
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:04:56.308038+00:00
-- url     : https://prove2.me/submissions/7d271f91-6875-4bf4-8a9f-3f51bb2dd239

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


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
    {f : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f b) :
    IsWeightedHomogeneous (tDeg ι) (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) b := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  rw [Geo.mConeMap, aeval_monomial, Finsupp.prod, MvPolynomial.algebraMap_apply]
  have hb : b = 0 + ∑ p ∈ m.support, m p • tDeg ι p.1 := by
    rw [zero_add, ← hf (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum]
    rfl
  rw [hb]
  refine (isWeightedHomogeneous_C _ _).mul (IsWeightedHomogeneous.prod _ _ _ fun p _ ↦ ?_)
  have h := ((isWeightedHomogeneous_C (tDeg ι) (flatCone x p)).mul
    (isWeightedHomogeneous_X (AlgebraicClosure ℚ) (tDeg ι) p.1)).pow (m p)
  rwa [zero_add] at h
end GroundTheory.Heights₂.Heights.OrbitCurve
