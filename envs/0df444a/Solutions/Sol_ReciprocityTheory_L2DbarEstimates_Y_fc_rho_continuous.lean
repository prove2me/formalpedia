-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_rho_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:54:48.299655+00:00
-- url     : https://prove2.me/submissions/23bc14fc-5c4f-41fc-a423-d2514ca46a1e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_rho_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mem_O
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_contDiffOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : Continuous (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hi0 : (x0 : Y) ∈ (A.chart (A.pick x0)).source := A.mem_pick _
  have hev : (fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) /
      ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) =ᶠ[𝓝 x0]
      fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x0) x) /
        ‖(fderiv ℂ (A.zLoc w0 s (A.pick x0)) (A.chart (A.pick x0) x)).det‖ ^ 2 := by
    have hU : ∀ᶠ x : A.Mset w0 s De in 𝓝 x0, (x : Y) ∈ (A.chart (A.pick x0)).source :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((A.chart (A.pick x0)).open_source.mem_nhds hi0)
    filter_upwards [hU] with x hx
    exact fc_rho_eq A hD x.2 (A.pick x0) hx
  refine ContinuousAt.congr ?_ hev.symm
  set i := A.pick (x0 : Y) with hidef
  have hph : ContinuousAt (fun y => A.ph A.kap i y) (x0 : Y) := by
    have h1 : ContinuousAt (A.ph A.kap i ∘ (A.chart i).symm) (A.chart i x0) :=
      ((A.smooth_ph A.kap i).continuousOn).continuousAt
        ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi0))
    have h2 := h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl
    refine h2.congr ?_
    filter_upwards [(A.chart i).open_source.mem_nhds hi0] with y hy
    simp only [Function.comp_apply, (A.chart i).left_inv hy]
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO := fc_mem_O A x0 i hi0
  have hdetc : ContinuousAt (fun y => (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det) (x0 : Y) := by
    have h1 : ContinuousAt (fderiv ℂ (A.zLoc w0 s i)) (A.chart i x0) :=
      ((fc_zLoc_contDiffOn A hD i).continuousOn_fderiv_of_isOpen hO (by simp)).continuousAt
        (hO.mem_nhds hmO)
    exact ContinuousLinearMap.continuous_det.continuousAt.comp
      (h1.comp_of_eq ((A.chart i).continuousAt hi0) rfl)
  have hne := fc_jz_det_ne A hD hF x0.2 i hi0
  have hFc : ContinuousAt (fun y => Real.exp (A.ph A.kap i y) /
      ‖(fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det‖ ^ 2) (x0 : Y) :=
    (Real.continuous_exp.continuousAt.comp hph).div ((continuous_norm.continuousAt.comp hdetc).pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  exact hFc.comp continuous_subtype_val.continuousAt
end ReciprocityTheory.L2DbarEstimates.Y
