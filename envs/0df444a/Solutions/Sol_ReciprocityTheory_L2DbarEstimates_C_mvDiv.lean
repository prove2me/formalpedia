-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mvDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:41.759543+00:00
-- url     : https://prove2.me/submissions/066fa505-ca6c-45ab-b223-f88784e30edc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MvDivIntegrand
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mvPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : MVDivStatement := by
  intro n hn
  have hpow := mvPow n n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → V n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))
    with hf
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    (by fun_prop : Measurable fun z : V n => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))))
  have hmono : Monotone f := by
    intro k m hkm z
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
    apply Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)) _
      (neg_nonpos.mpr (Nat.cast_nonneg _))
    gcongr
  have hinf : ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ∞ := by
    by_contra h
    have hlt := lt_top_iff_ne_top.mpr h
    have hint : IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * (n : ℝ))) (ball 0 1) := by
      refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal ?_).mpr hlt⟩
      exact ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _
    exact lt_irrefl _ (hpow.mp hint)
  have hsup : ∀ z : V n, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ ⨆ k, f k z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
      exact zero_le
    · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : Tendsto (fun k : ℕ => ‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖z‖ ^ 2 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.rpow_const (p := -(n : ℝ)) (Or.inl (by positivity))
      have ht : Tendsto (fun k : ℕ => f k z) atTop (𝓝 (ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))))) := by
        show Tendsto (fun k : ℕ => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))) atTop _
        apply ENNReal.tendsto_ofReal
        convert h2 using 2
        rw [add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        push_cast
        ring
      exact le_of_tendsto' ht (fun k => le_iSup (fun k => f k z) k)
  have hbig : ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z = ∞ := by
    rw [← lintegral_iSup hmeas hmono]
    refine top_le_iff.mp ?_
    rw [← hinf]
    exact lintegral_mono hsup
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  have hM : (M : ℝ≥0∞) < ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z := by
    rw [hbig]
    exact ENNReal.coe_lt_top
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hM
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with δ hδ
  refine hk.trans_le (lintegral_mono fun z => ?_)
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ.1)
    (by linarith [hδ.2]) (neg_nonpos.mpr (Nat.cast_nonneg _))
end ReciprocityTheory.L2DbarEstimates.C
