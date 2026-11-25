-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_cxHessian_sum_d84903d63063
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:19.484914+00:00
-- url     : https://prove2.me/submissions/bd08306f-de29-442f-af86-d9e82ec13cc5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution {D : ℕ} {T : Type} [Fintype T] (f : T → (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hf : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (f t) y') :
    cxHessian (fun y' => ∑ t, f t y') y = ∑ t, cxHessian (f t) y := by
  have h1 : fderiv ℝ (fun y' => ∑ t, f t y') =ᶠ[𝓝 y] fun y' => ∑ t, fderiv ℝ (f t) y' := by
    filter_upwards [eventually_all.mpr hf] with y' hy'
    exact fderiv_fun_sum fun t _ => (hy' t).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => ∑ t, f t y')) y = ∑ t, fderiv ℝ (fderiv ℝ (f t)) y := by
    rw [h1.fderiv_eq]
    exact fderiv_fun_sum fun t _ =>
      ((hf t).self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  simp only [cxHessian, h2, FunLike.coe_sum, Finset.sum_apply, Matrix.sum_apply]
  push_cast
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
end GroundTheory.Heights₂.Heights.PointsBilinear
