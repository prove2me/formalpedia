-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemSG_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:04.283483+00:00
-- url     : https://prove2.me/submissions/bda8306c-bb85-481a-a20b-3c34ba347829

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_im
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
theorem _root_.solution {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (b₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    (lemSG b).det = LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) *
      b₀.toBasis.det b * b₀.toBasis.det b := by
  have hG : lemSG b = (b₀.toBasis.toMatrix b)ᵀ *
      (LinearMap.toMatrix b₀.toBasis b₀.toBasis (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _))ᵀ *
      b₀.toBasis.toMatrix b := by
    ext i k
    have e1 : lemSG b i k = inner ℝ (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) := by
      simp only [lemSG, Matrix.of_apply, lemS_Hf_im, lemSJ_apply]
    have e2 : ∀ j, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) =
        ∑ l, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b₀ l)) * inner ℝ (b₀ l) (b i) := by
      intro j
      conv_lhs => rw [← b₀.sum_repr' (b i)]
      rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, real_inner_smul_right, mul_comm]
    rw [e1, ← b₀.sum_inner_mul_inner (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i))]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.coe_toBasis, e2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, real_inner_comm (b₀ j) (b k)]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    LinearMap.det_toMatrix, Module.Basis.det_apply]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
