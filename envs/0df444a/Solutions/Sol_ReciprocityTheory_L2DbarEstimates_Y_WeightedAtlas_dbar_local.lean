-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.dbar_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:24.736585+00:00
-- url     : https://prove2.me/submissions/8e51470c-ad23-49d7-9155-645ab0627273

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_dbarAt_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mem_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_trans_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chiC_of_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (β : V n → ℝ) (hβ : ContDiff ℝ ∞ β) (la' : La) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (F : ι → Y → ℂ) (c : ℂ)
    (hF : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] fun v =>
      c * (A.chiC i β ((A.chart j).symm v) : ℂ) * A.g la' j i ((A.chart j).symm v))
    (ξ : Fin n → ℂ) :
    A.dbarAt j F y ξ = c * A.g la' j i y *
      dbv (fderiv ℝ (fun u => (β u : ℂ)) (A.chart i y))
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)) := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : DifferentiableAt ℂ Φ v0 := (A.trans_contDiffAt hj hi).differentiableAt (by norm_num)
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set G := A.g la' j i ∘ (A.chart j).symm
  have hG : DifferentiableAt ℂ G v0 :=
    (A.holo_g la' j i).differentiableAt hO
  set βc : V n → ℂ := fun u => (β u : ℂ)
  have hβc : ContDiff ℝ ∞ βc := Complex.ofRealCLM.contDiff.comp hβ
  have hβd : DifferentiableAt ℝ βc (Φ v0) := hβc.differentiable (by norm_cast) _
  have hf1 : DifferentiableAt ℝ (fun v => c * (βc ∘ Φ) v) v0 :=
    (hβd.comp v0 (hΦ.restrictScalars ℝ)).const_mul c
  have hev : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 v0] fun v => c * (βc ∘ Φ) v * G v := by
    filter_upwards [hF, hO] with v hv hvO
    rw [hv, A.chiC_of_mem hvO.2]
    simp only [Function.comp, βc, G, Φ]
  rw [dbarAt_eq, hev.fderiv_eq, fderiv_fun_mul hf1 (hG.restrictScalars ℝ), dbv_add, dbv_smul,
    dbv_smul, dbv_holo hG, mul_zero, zero_add, fderiv_const_mul (hβd.comp v0 (hΦ.restrictScalars ℝ)),
    dbv_smul, dbv_comp hβd hΦ, hΦv]
  simp only [G, Function.comp, v0, (A.chart j).left_inv hj]
  ring
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
