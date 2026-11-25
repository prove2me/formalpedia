-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_det_jz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:08.81807+00:00
-- url     : https://prove2.me/submissions/1b158abe-f200-442f-b657-77a60a298fd3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O
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
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i j : ι) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) :
    (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det = (fderiv ℂ (A.zLoc w0 s j) (A.chart j y)).det * A.g A.kap i j y := by
  have hT : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
    simp only [Function.comp, (A.chart i).left_inv hi]
  have hov : IsOpen (ovl A.chart i j) :=
    (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
  have hx0ov : A.chart i y ∈ ovl A.chart i j := by
    refine ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i y) ∈ (A.chart j).source
    rw [(A.chart i).left_inv hi]
    exact hj
  have hev : A.zLoc w0 s i =ᶠ[𝓝 (A.chart i y)] A.zLoc w0 s j ∘ (A.chart j ∘ (A.chart i).symm) := by
    filter_upwards [hov.mem_nhds hx0ov] with v hv
    simp only [Function.comp]
    rw [fc_zLoc_eq A hD i v hv.1, fc_zLoc_eq A hD j _ ((A.chart j).map_source hv.2),
      (A.chart j).left_inv hv.2]
  have hdT : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
    (A.holo_trans i j).differentiableAt (hov.mem_nhds hx0ov)
  have hdz : DifferentiableAt ℂ (A.zLoc w0 s j) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
    rw [hT]
    have hO := fc_isOpen_O A (De := De) hD j
    have hm : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' A.Mset w0 s De := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j y) ∈ A.Mset w0 s De
      rw [(A.chart j).left_inv hj]
      exact hy
    exact ((fc_zLoc_contDiffOn A hD j).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hm)
  rw [hev.fderiv_eq, fderiv_comp (A.chart i y) hdz hdT, hT, A.g_kap i j y hi hj]
  change LinearMap.det (((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)).comp
      (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) =
    LinearMap.det ((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)) : V n →ₗ[ℂ] V n) *
      LinearMap.det ((fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →ₗ[ℂ] V n)
  exact LinearMap.det_comp ((fderiv ℂ (A.zLoc w0 s j) (A.chart j y)) : V n →ₗ[ℂ] V n)
    ((fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) : V n →ₗ[ℂ] V n)
end ReciprocityTheory.L2DbarEstimates.Y
