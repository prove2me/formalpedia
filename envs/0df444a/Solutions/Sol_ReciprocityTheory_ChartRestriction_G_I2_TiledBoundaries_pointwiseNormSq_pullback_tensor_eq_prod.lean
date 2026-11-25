-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.pointwiseNormSq_pullback_tensor_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:49.678971+00:00
-- url     : https://prove2.me/submissions/47ddff1c-9743-4070-8e09-2aa085d9909d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (s0 X π s) v = ∏ k, X.ptN2 1 s (fun _ => π (v k)) := by
  unfold PT.ptN2 s0
  rw [Finset.prod_mul_distrib, norm_prod, ← Finset.prod_pow, ← Real.exp_sum]
  congr 2
  simp only [HC, Fin.sum_univ_one, hπ.2.2.1, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
