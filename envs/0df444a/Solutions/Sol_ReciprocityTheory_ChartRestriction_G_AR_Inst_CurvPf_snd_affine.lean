-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.snd_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:01.969806+00:00
-- url     : https://prove2.me/submissions/bd6bb0ce-eba1-4f9e-b412-1f8f39873415

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : F → ℝ) (c : F) (L : E →L[ℝ] F) (x : E) (hh : ContDiffAt ℝ 2 h (c + L x))
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h (c + L y))) x w w = fderiv ℝ (fderiv ℝ h) (c + L x) (L w) (L w) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h (c + L y) := by
    have h1 : ∀ᶠ z in 𝓝 (c + L x), DifferentiableAt ℝ h z :=
      (hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hg : ContinuousAt (fun y => c + L y) x := (continuous_const.add L.continuous).continuousAt
    exact hg.eventually h1
  have heq : fderiv ℝ (fun y => h (c + L y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (c + L y)).comp L := by
    filter_upwards [hd] with y hy
    have hgd : HasFDerivAt (fun y => c + L y) L y := (L.hasFDerivAt).const_add c
    exact (hy.hasFDerivAt.comp y hgd).fderiv
  rw [heq.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ h) (c + L x) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : HasFDerivAt (fun y => fderiv ℝ h (c + L y)) ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L) x :=
    hd2.hasFDerivAt.comp x ((L.hasFDerivAt).const_add c)
  have hG : HasFDerivAt (fun y => (fderiv ℝ h (c + L y)).comp L)
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L)) x :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp x hF
  rw [hG.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
