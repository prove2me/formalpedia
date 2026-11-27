-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.levi_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:36.217725+00:00
-- url     : https://prove2.me/submissions/0f2a4895-3c5e-4ae2-8d4f-26b11c951fa2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mem_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_trans_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffAt_two_of_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_log_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum


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
theorem _root_.solution (la : La) (f : Y → ℝ) (hf : A.SmoothFn f) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt j (fun x => A.ph la j x + f x) y ξ =
      A.leviAt i (fun x => A.ph la i x + f x) y
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)).ofLp := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : ContDiffAt ℂ 2 Φ v0 := A.trans_contDiffAt hj hi
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set h : V n → ℝ := fun u => A.ph la i ((A.chart i).symm u) + f ((A.chart i).symm u)
  have hh : ContDiffAt ℝ 2 h (Φ v0) := by
    rw [hΦv]
    exact (((A.smooth_ph la i).add (hf i)).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).of_le (by norm_cast)
  set G := A.g la j i ∘ (A.chart j).symm
  have hG : ContDiffAt ℂ 2 G v0 :=
    contDiffAt_two_of_holo (A.isOpen_ovl j i) (A.holo_g la j i) hv0
  have hG0 : G v0 ≠ 0 := by
    simp only [G, Function.comp, v0, (A.chart j).left_inv hj]; exact A.g_ne la j i y hj hi
  set u2 : Fin 2 → V n → ℝ := ![fun v => h (Φ v), fun v => Real.log (Complex.normSq (G v))]
  have hu2 : ∀ k, ContDiffAt ℝ 2 (u2 k) v0 := by
    intro k; fin_cases k
    · exact hh.comp v0 (hΦ.restrict_scalars ℝ)
    · exact (contDiffAt_normSq_comp hG).log (Complex.normSq_pos.2 hG0).ne'
  have hev : (fun v => ((A.ph la j ((A.chart j).symm v) + f ((A.chart j).symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((∑ k, u2 k v : ℝ) : ℂ) := by
    filter_upwards [hO] with v hv
    have hxj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hxi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    have hsy : (A.chart i).symm (Φ v) = (A.chart j).symm v := by
      simp only [Φ, Function.comp]; exact (A.chart i).left_inv hxi
    have hne : ‖A.g la j i ((A.chart j).symm v)‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la j i _ hxj hxi)
    simp only [Fin.sum_univ_two, u2, Matrix.cons_val_zero, Matrix.cons_val_one, h, hsy, G,
      Function.comp, A.ph_trans la j i _ hxj hxi, Complex.normSq_eq_norm_sq]
    push_cast; ring
  unfold leviAt
  rw [leviV_congr hev, leviV_ofReal_sum hu2, Fin.sum_univ_two]
  have e1 : u2 0 = fun v => h (Φ v) := rfl
  have e2 : u2 1 = fun v => Real.log (Complex.normSq (G v)) := rfl
  rw [e1, e2, leviV_log_normSq hG hG0, add_zero]
  have hc := leviV_comp (f := fun u => ((h u : ℝ) : ℂ)) (Φ := Φ) (y := v0) ?_ hΦ ξ
  · rw [show (fun v => ((h (Φ v) : ℝ) : ℂ)) = (fun u => ((h u : ℝ) : ℂ)) ∘ Φ from rfl, hc, hΦv]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hh
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
