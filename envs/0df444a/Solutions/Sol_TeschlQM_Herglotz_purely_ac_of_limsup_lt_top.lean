-- Prove2me | solution 1 for TeschlQM.Herglotz.purely_ac_of_limsup_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:45:32.228298+00:00
-- url     : https://prove2.me/submissions/c61f51cc-703e-4263-af49-026c54ff65de

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter
open scoped ENNReal Topology

set_option autoImplicit false

namespace F61F2D77

open Metric

lemma integrable_inv (μ : Measure ℝ) [IsFiniteMeasure μ] (t ε : ℝ) (hε : 0 < ε) :
    Integrable (fun s : ℝ => ((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))⁻¹) μ := by
  have hne : ∀ s : ℝ, ((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I)) ≠ 0 := by
    intro s h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcont : Continuous (fun s : ℝ => ((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))⁻¹) := by
    apply Continuous.inv₀ (by fun_prop) hne
  refine Integrable.of_bound hcont.aestronglyMeasurable (1 / ε) (Eventually.of_forall ?_)
  intro s
  rw [norm_inv]
  have : ε ≤ ‖((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))‖ := by
    have h1 := Complex.abs_im_le_norm ((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))
    simp at h1
    rw [abs_of_pos hε] at h1
    exact h1
  rw [one_div]
  exact inv_anti₀ hε this

lemma im_formula (t ε s : ℝ) :
    (((s : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))⁻¹).im = ε / ((s - t) ^ 2 + ε ^ 2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  ring

lemma ball_le (μ : Measure ℝ) [IsFiniteMeasure μ] (t ε : ℝ) (hε : 0 < ε) :
    μ (closedBall t ε) ≤ ENNReal.ofReal (2 * ε) *
      ENNReal.ofReal (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im := by
  have hint := integrable_inv μ t ε hε
  have him : (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im
      = ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ := by
    unfold TeschlQM.Herglotz.borelTransform
    have := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at this
    rw [← this]
    simp_rw [im_formula]
  have gnn : ∀ s : ℝ, 0 ≤ ε / ((s - t) ^ 2 + ε ^ 2) := fun s => by positivity
  have gint : Integrable (fun s : ℝ => ε / ((s - t) ^ 2 + ε ^ 2)) μ := by
    refine (hint.im).congr (Eventually.of_forall fun s => ?_)
    exact im_formula t ε s
  rw [him, ofReal_integral_eq_lintegral_ofReal gint (Eventually.of_forall gnn)]
  have key : ENNReal.ofReal (1 / (2 * ε)) * μ (closedBall t ε) ≤
      ∫⁻ s, ENNReal.ofReal (ε / ((s - t) ^ 2 + ε ^ 2)) ∂μ := by
    rw [← lintegral_indicator_const measurableSet_closedBall]
    apply lintegral_mono
    intro s
    by_cases hs : s ∈ closedBall t ε
    · rw [Set.indicator_of_mem hs]
      apply ENNReal.ofReal_le_ofReal
      have hd : (s - t) ^ 2 ≤ ε ^ 2 := by
        rw [mem_closedBall, Real.dist_eq] at hs
        have := abs_le.mp hs
        nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [Set.indicator_of_notMem hs]
      simp
  calc μ (closedBall t ε) = ENNReal.ofReal (2 * ε) * (ENNReal.ofReal (1 / (2 * ε)) * μ (closedBall t ε)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

end F61F2D77

open F61F2D77 in
open Metric in
theorem f61f2d77_solution_aux (μ : Measure ℝ) [IsFiniteMeasure μ] (I : Set ℝ)
    (h : ∀ t ∈ I, limsup (fun ε : ℝ => ENNReal.ofReal
        (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) < ⊤) :
    μ.restrict I ≪ volume := by
  let v := Besicovitch.vitaliFamily μ
  let S : ℕ → Set ℝ := fun k =>
    {x | ∃ᶠ a in v.filterAt x, μ a ≤ ((k : NNReal) • (volume : Measure ℝ)) a}
  have hcover : I ⊆ ⋃ k, S k := by
    intro t ht
    obtain ⟨b, hLb, hbtop⟩ := exists_between (h t ht)
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hbtop.ne
    have hev := eventually_lt_of_limsup_lt hLb
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    show ∃ᶠ a in v.filterAt t, μ a ≤ ((k : NNReal) • (volume : Measure ℝ)) a
    apply (Besicovitch.tendsto_filterAt μ t).frequently
    apply Eventually.frequently
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : (0 : ℝ) < r := hrpos
    refine (ball_le μ t r hrpos').trans ?_
    simp only [Measure.coe_nnreal_smul_apply, Real.volume_closedBall, ENNReal.coe_natCast]
    rw [mul_comm]
    gcongr
    exact (hr.trans hk).le
  refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
  rw [Measure.restrict_apply hN]
  apply measure_mono_null (Set.inter_subset_inter_right N hcover)
  rw [Set.inter_iUnion]
  apply measure_iUnion_null
  intro k
  have := v.measure_le_of_frequently_le ((k : NNReal) • (volume : Measure ℝ))
    (Measure.AbsolutelyContinuous.refl _) (N ∩ S k) (fun x hx => hx.2)
  refine le_antisymm (this.trans ?_) (by simp)
  simp only [Measure.coe_nnreal_smul_apply]
  rw [measure_mono_null Set.inter_subset_left hN0, mul_zero]

open MeasureTheory Filter ENNReal Topology TeschlQM.Herglotz in
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (I : Set ℝ)
    (hI : MeasurableSet I)
    (h : ∀ t ∈ I, limsup (fun ε : ℝ => ENNReal.ofReal
        (borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) < ⊤) :
    μ.restrict I ≪ volume := by
  exact f61f2d77_solution_aux μ I h
