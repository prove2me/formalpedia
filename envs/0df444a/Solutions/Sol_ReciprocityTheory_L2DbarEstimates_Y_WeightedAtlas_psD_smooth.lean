-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.psD_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:49.973127+00:00
-- url     : https://prove2.me/submissions/8b2dccd6-1f4a-4294-a626-432bb66558c9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffOn_of_holo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_sqn_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_sqn_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_holo_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1)
    (η : ℝ) {δ : ℝ} (hδ : 0 < δ) : A.SmoothFn (A.psD L w s ps1 η δ) := by
  intro i
  set φ := A.chart i
  have hb : ContDiffOn ℝ ∞ (fun v => A.ph L i (φ.symm v)) φ.target := A.smooth_ph L i
  have hn2 : ∀ {m : ℕ} (u : Fin m → ι → Y → ℂ), (∀ k, A.IsSec L (u k)) →
      ContDiffOn ℝ ∞ (fun v => (∑ k, ‖u k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v)))
        φ.target := fun u hu =>
    (ContDiffOn.sum fun k _ => (contDiff_norm_sq ℝ).comp_contDiffOn
      (contDiffOn_of_holo φ.open_target (A.holo_chart (hu k) i))).mul
      (Real.contDiff_exp.comp_contDiffOn hb.neg)
  have heq : ∀ v ∈ φ.target, (A.psD L w s ps1 η δ ∘ φ.symm) v =
      ps1 (φ.symm v) + η * Real.log ((∑ k, ‖w k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v))) + n * Real.log ((∑ k, ‖s k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v)) + δ) := by
    intro v hv
    have hx := φ.map_target hv
    simp only [Function.comp, psD, A.sqn_chart L w hD.sec_w i hx, A.sqn_chart L s hD.sec_s i hx]
  refine ContDiffOn.congr ?_ heq
  refine ((hps1 i).add (contDiffOn_const.mul ((hn2 w hD.sec_w).log ?_))).add
    (contDiffOn_const.mul (((hn2 s hD.sec_s).add contDiffOn_const).log ?_))
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L w hD.sec_w i hx]; exact (A.aap_sqn_pos hD _).ne'
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L s hD.sec_s i hx]; have := A.aap_sqn_nonneg L s (φ.symm v); positivity
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
