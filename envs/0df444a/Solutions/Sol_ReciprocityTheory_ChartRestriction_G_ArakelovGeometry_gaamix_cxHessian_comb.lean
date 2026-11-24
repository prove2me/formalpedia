-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:27.111607+00:00
-- url     : https://prove2.me/submissions/e92a8fec-f8f1-4296-a2d4-b4a15aa761bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (s u : ℝ)
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => s * a y' + u * b y') :
    cxHessian ψ y = (s : ℂ) • cxHessian a y + (u : ℂ) • cxHessian b y := by
  have hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y' := by
    filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3
    rw [h1.fderiv_eq]
    have d2 := h2.differentiableAt (by norm_num)
    have d3 := h3.differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv
  have hH : fderiv ℝ (fderiv ℝ ψ) y =
      s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y := by
    rw [hd.fderiv_eq]
    have d2 := (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have d3 := (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv
  ext i j
  simp only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
