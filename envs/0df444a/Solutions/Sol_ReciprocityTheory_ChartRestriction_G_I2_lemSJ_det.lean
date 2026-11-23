-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemSJ_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:04.759416+00:00
-- url     : https://prove2.me/submissions/9d837ef6-7d92-4dc2-90bc-67af25a3b3f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemSJ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| = 1 := by
  have h2 : ∀ x : EuclideanSpace ℂ ι, (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (lemSJ x) = -x := by
    intro x
    rw [lemSJ_apply, lemSJ_apply, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  have hJJ : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) * lemSJ = -1 :=
    LinearMap.ext fun x => h2 x
  have h4 : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    have e : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = (lemSJ * lemSJ) * (lemSJ * lemSJ) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hJJ, neg_one_mul, neg_neg]
  have hd : LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    rw [← map_pow, h4, map_one]
  have ha : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| ^ 4 = 1 := by
    rw [← abs_pow, hd, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).1 ha
end ReciprocityTheory.ChartRestriction.G.I2
