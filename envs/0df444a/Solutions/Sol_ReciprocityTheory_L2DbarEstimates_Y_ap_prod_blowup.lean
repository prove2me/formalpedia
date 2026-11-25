-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ap_prod_blowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:45.742061+00:00
-- url     : https://prove2.me/submissions/ab7b898a-b0ba-46a5-9f08-1980b6700910

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apraW_anti
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apra_slice
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apra_base
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apra_blow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (d k : ℕ) (hd : 1 ≤ d) (hMVd : MVStatement d) (hMVk : MVStatement k)
    (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V d × V k → ℂ,
      DifferentiableOn ℂ u (Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε) →
      ENNReal.ofReal (M * ‖u 0‖ ^ 2) ≤
        ∫⁻ z in Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε,
          ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  have hvol : volume (ball (0 : V k) ε) ≠ 0 := (measure_ball_pos volume (0 : V k) hε).ne'
  have hsup : ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by
    rw [← ENNReal.mul_iSup, apra_blow d hd hMVI ε hε, ENNReal.mul_top hvol]
  have hlt : ENNReal.ofReal M < ⨆ n : ℕ, volume (ball (0 : V k) ε) *
      ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ := by
    rw [hsup]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun τ hτ hτ0 u hu => ?_⟩
  have hIτ : ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ ≤ ∫⁻ x : V d, apraW d ε τ ‖x‖ :=
    lintegral_mono fun x => apraW_anti d ε hτ hτ0 _
  have hslice : ∀ ζ ∈ ball (0 : V k) ε,
      ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) * ∫⁻ x : V d, apraW d ε τ ‖x‖ ≤
        ∫⁻ x in ball (0 : V d) ε,
          ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) :=
    fun ζ hζ => apra_slice d k hMVd ε τ u hu ζ hζ
  have hbase := apra_base k hMVk ε (fun ζ => u (0, ζ))
    (hu.comp ((differentiableOn_const (0 : V d)).prodMk differentiableOn_id)
      (fun ζ hζ => ⟨mem_ball_self hε, hζ⟩))
  have hmeasF : AEMeasurable
      (fun z : V d × V k => ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))))
      ((volume.restrict (ball (0 : V d) ε)).prod (volume.restrict (ball (0 : V k) ε))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hu' : AEMeasurable u (volume.restrict (ball (0 : V d) ε ×ˢ ball (0 : V k) ε)) :=
      hu.continuousOn.aemeasurable (measurableSet_ball.prod measurableSet_ball)
    exact ((hu'.norm.pow_const 2).mul (((measurable_fst.norm.pow_const 2).max
      measurable_const).pow_const _).aemeasurable).ennreal_ofReal
  have hfub : ∫⁻ z in ball (0 : V d) ε ×ˢ ball (0 : V k) ε,
      ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) =
      ∫⁻ ζ in ball (0 : V k) ε, ∫⁻ x in ball (0 : V d) ε,
        ENNReal.ofReal (‖u (x, ζ)‖ ^ 2 * (max (‖x‖ ^ 2) τ) ^ (-(d : ℝ))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeasF]
  rw [hfub]
  calc ENNReal.ofReal (M * ‖u 0‖ ^ 2)
      = ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul' (by positivity), mul_comm]
        rfl
    _ ≤ ENNReal.ofReal (‖u (0, 0)‖ ^ 2) *
          (volume (ball (0 : V k) ε) * ∫⁻ x : V d, apraW d ε τ ‖x‖) :=
        mul_le_mul' le_rfl (hn.le.trans (mul_le_mul' le_rfl hIτ))
    _ = (ENNReal.ofReal (‖u (0, 0)‖ ^ 2) * volume (ball (0 : V k) ε)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := (mul_assoc _ _ _).symm
    _ ≤ (∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2)) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := mul_le_mul' hbase le_rfl
    _ ≤ ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖u (0, ζ)‖ ^ 2) *
          ∫⁻ x : V d, apraW d ε τ ‖x‖ := lintegral_mul_const_le _ _
    _ ≤ _ := setLIntegral_mono' measurableSet_ball hslice
end ReciprocityTheory.L2DbarEstimates.Y
