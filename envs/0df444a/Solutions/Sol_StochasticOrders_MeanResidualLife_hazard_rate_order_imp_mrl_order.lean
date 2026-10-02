-- Prove2me | solution 1 for StochasticOrders.MeanResidualLife.hazard_rate_order_imp_mrl_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:32:22.690019+00:00
-- url     : https://prove2.me/submissions/30d18382-eb31-4efa-902f-6dc9a9fec015

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder

set_option autoImplicit false

open MeasureTheory in
lemma p44b_layer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) (t : ℝ) :
    ∫⁻ ω in {ω | t < X ω}, ENNReal.ofReal (X ω - t) ∂μ
      = ∫⁻ s in Set.Ioi 0, μ {ω | t + s < X ω} := by
  have hS : MeasurableSet {ω | t < X ω} := measurableSet_lt measurable_const hX
  rw [← lintegral_indicator hS]
  have hfun : ({ω | t < X ω} : Set Ω).indicator (fun ω => ENNReal.ofReal (X ω - t))
      = fun ω => ENNReal.ofReal (max (X ω - t) 0) := by
    funext ω
    by_cases hω : t < X ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | t < X ω} from hω),
        max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | t < X ω} from hω),
        max_eq_right (by linarith), ENNReal.ofReal_zero]
  rw [hfun, lintegral_eq_lintegral_meas_lt (f := fun ω => max (X ω - t) 0) μ
    (ae_of_all _ fun ω => le_max_right _ _)
    (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0:ℝ) < s := hs
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, lt_max_iff]
  constructor
  · rintro (h1 | h1)
    · linarith
    · linarith
  · intro h1; left; linarith

open MeasureTheory in
lemma p44b_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) (t : ℝ) :
    ∫ ω in {ω | t < X ω}, (X ω - t) ∂μ
      = (∫⁻ s in Set.Ioi 0, μ {ω | t + s < X ω}).toReal := by
  have hS : MeasurableSet {ω | t < X ω} := measurableSet_lt measurable_const hX
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' hS).mpr (ae_of_all _ fun ω (hω : t < X ω) => (sub_pos.2 hω).le))
    (hX.sub measurable_const).aestronglyMeasurable, p44b_layer μ X hX t]

open MeasureTheory in
lemma p44b_fin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hXi : Integrable X μ) (t : ℝ) :
    (∫⁻ s in Set.Ioi 0, μ {ω | t + s < X ω}) ≠ ⊤ := by
  rw [← p44b_layer μ X hX t]
  exact (lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
    (hXi.sub (integrable_const t)).lintegral_lt_top).ne

open MeasureTheory StochasticOrders.MeanResidualLife in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν) (h : HazardRateOrder μ ν X Y) :
    MrlOrder μ ν X Y := by
  intro t
  unfold mrl
  have hSY : MeasurableSet {ω | t < Y ω} := measurableSet_lt measurable_const hY
  have hnn : 0 ≤ ∫ ω in {ω | t < Y ω}, (Y ω - t) ∂ν :=
    setIntegral_nonneg hSY fun ω (hω : t < Y ω) => (sub_pos.2 hω).le
  by_cases ha : 0 < (μ {ω | t < X ω}).toReal
  · have hb : 0 < (ν {ω | t < Y ω}).toReal := by
      by_contra hb
      have hb0 : ν {ω | t < Y ω} = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm (not_lt.1 hb) ENNReal.toReal_nonneg)
          with h0 | h0
        · exact h0
        · exact absurd h0 (measure_ne_top _ _)
      have hn : ∀ n : ℕ, ν {ω | t - n < Y ω} = 0 := by
        intro n
        have := h (t - n) t (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
        unfold survival at this
        rw [hb0, mul_zero, nonpos_iff_eq_zero, mul_eq_zero] at this
        rcases this with h0 | h0
        · exact absurd (by rw [h0]; rfl) ha.ne'
        · exact h0
      have hU : (Set.univ : Set Ω') ⊆ ⋃ n : ℕ, {ω | t - n < Y ω} := by
        intro ω _
        obtain ⟨n, hn⟩ := exists_nat_gt (t - Y ω)
        exact Set.mem_iUnion.2 ⟨n, show t - n < Y ω by linarith⟩
      have := measure_mono_null hU (measure_iUnion_null hn)
      simp at this
    rw [if_pos ha, if_pos hb, p44b_int μ X hX t, p44b_int ν Y hY t,
      div_le_div_iff₀ ha hb, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
    apply ENNReal.toReal_mono (ENNReal.mul_ne_top (p44b_fin ν Y hY hYi t) (measure_ne_top _ _))
    rw [← lintegral_mul_const' _ _ (measure_ne_top ν _),
      ← lintegral_mul_const' _ _ (measure_ne_top μ _)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0:ℝ) < s := hs
    have := h t (t + s) (by linarith)
    unfold survival at this
    rw [mul_comm (ν {ω | t + s < Y ω})]
    exact this
  · rw [if_neg ha]
    split_ifs
    · exact div_nonneg hnn ENNReal.toReal_nonneg
    · exact le_rfl
