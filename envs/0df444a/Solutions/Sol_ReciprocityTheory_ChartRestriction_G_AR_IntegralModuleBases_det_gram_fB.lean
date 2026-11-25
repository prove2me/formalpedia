-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.det_gram_fB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:02.609192+00:00
-- url     : https://prove2.me/submissions/d5be7291-2dd0-4680-bee3-6732f2b6ea46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_det_toMatrix_sq
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_polar_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (Matrix.gram ℝ fun i => fB B (e i)).det = A.det := by
  have hG : Matrix.gram ℝ (fun i => fB B (e i)) =
      (Matrix.of fun k j => ((e j k : ℤ) : ℝ))ᵀ * A * (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) := by
    ext i j
    rw [Matrix.gram_apply, ← polar_eq A B hAB]
    simp only [polar, toReal, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hE : (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) =
      ((Pi.basisFun ℤ (Fin d)).toMatrix e).map (Int.cast : ℤ → ℝ) := by
    ext k j
    simp [Module.Basis.toMatrix_apply]
  have hsq := det_toMatrix_sq e
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hE, ← Int.cast_det]
  linear_combination A.det * hsq
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
