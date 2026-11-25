-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:27.30617+00:00
-- url     : https://prove2.me/submissions/6578d491-435d-4474-985f-6a62e87815f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsAddFirst
theorem _root_.solution {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => fderiv ℝ a y' + fderiv ℝ b y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), ha, hb] with y' h1 h2 h3
    rw [h1]
    exact ((h2.differentiableAt (by norm_num)).hasFDerivAt.add
      (h3.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have da2 : DifferentiableAt ℝ (fderiv ℝ a) y :=
    (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have db2 : DifferentiableAt ℝ (fderiv ℝ b) y :=
    (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ b) y := by
    rw [h1.fderiv_eq]
    exact (da2.hasFDerivAt.add db2.hasFDerivAt).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, add_apply]
  push_cast
  ring
end PtsAddFirst
end GroundTheory.Heights₂.Heights.Inter
