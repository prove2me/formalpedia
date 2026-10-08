-- Prove2me | solution 1 for TeschlQM.Herglotz.poisson_upper_of_ball_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T21:28:45.128267+00:00
-- url     : https://prove2.me/submissions/c3963439-8583-4a02-b726-165630d1f2ad

import Theorems.Thm_TeschlQM_Herglotz_borelTransform_im
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t δ c ε : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      μ (Metric.ball t r) / volume (Metric.ball t r) ≤ ENNReal.ofReal c) :
    (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi ≤
      c + (ε / δ ^ 2) * (μ Set.univ).toReal / Real.pi := by
  let K : ℝ → ℝ := fun x => ε / ((x - t)^2 + ε^2)
  let a : ℝ := ε / δ^2
  let f : ℝ → ℝ := fun x => max (K x - a) 0
  have ha : 0 < a := by dsimp [a]; positivity
  have hKn : ∀ x, 0 ≤ K x := by intro x; dsimp [K]; positivity
  have hKd : ∀ x : ℝ, 0 < (x-t)^2 + ε^2 := by intro x; positivity
  have hKc : Continuous K := by
    unfold K
    exact continuous_const.div (by fun_prop) (fun x => ne_of_gt (hKd x))
  have hfc : Continuous f := hKc.sub continuous_const |>.max continuous_const
  have hfn : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have hfK : ∀ x, f x ≤ K x := by
    intro x
    exact max_le (by linarith) (hKn x)
  have hKb : ∀ x, K x ≤ 1 / ε := by
    intro x
    dsimp [K]
    calc
      ε / ((x-t)^2 + ε^2) ≤ ε / ε^2 :=
        div_le_div_of_nonneg_left hε.le (sq_pos_of_pos hε) (by nlinarith [sq_nonneg (x-t)])
      _ = 1 / ε := by field_simp
  have hKμ : Integrable K μ := by
    apply Integrable.of_bound hKc.aestronglyMeasurable (1 / ε)
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hKn x)]; exact hKb x
  have hfμ : Integrable f μ := hKμ.mono' hfc.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn x)]; exact hfK x)
  have hscale : ∀ x : ℝ, K x = ε⁻¹ * (1 + ((x-t)/ε)^2)⁻¹ := by
    intro x
    dsimp [K]
    field_simp
    <;> ring
  have hKv : Integrable K volume := by
    change Integrable (fun x => K x) volume
    simp_rw [hscale]
    exact ((integrable_inv_one_add_sq.comp_div hε.ne').comp_sub_right t).const_mul _
  have hKi : ∫ x, K x = Real.pi := by
    simp_rw [hscale]
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun x : ℝ => (1 + (x/ε)^2)⁻¹) t,
      Measure.integral_comp_div (fun x : ℝ => (1+x^2)⁻¹) ε,
      integral_univ_inv_one_add_sq,
      abs_of_pos hε, smul_eq_mul]
    field_simp
  have hfv : Integrable f volume := hKv.mono' hfc.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn x)]; exact hfK x)
  have hballs : ∀ r : ℝ, 0 < r → r < δ →
      μ (Metric.ball t r) ≤ ENNReal.ofReal c * volume (Metric.ball t r) := by
    intro r hr hrd
    apply (ENNReal.div_le_iff ?_ ?_).mp (hdensity r hr hrd)
    · rw [Real.volume_ball]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top
  have hsuper : ∀ y : ℝ, 0 < y →
      μ {x | y < f x} ≤ ENNReal.ofReal c * volume {x | y < f x} := by
    intro y hy
    have hlevel : {x | y < f x} = {x | (x-t)^2 < ε / (y+a) - ε^2} := by
      ext x
      simp only [mem_ofPred_eq, f, lt_max_iff, not_lt.mpr hy.le, or_false]
      dsimp only [K]
      rw [lt_sub_iff_add_lt, lt_div_iff₀ (hKd x)]
      have hyp : 0 < y+a := by positivity
      rw [lt_sub_iff_add_lt, lt_div_iff₀ hyp]
      constructor <;> intro h <;> nlinarith [h]
    rw [hlevel]
    by_cases hb : 0 < ε / (y+a) - ε^2
    · let r := Real.sqrt (ε / (y+a) - ε^2)
      have hr : 0 < r := Real.sqrt_pos.2 hb
      have hrs : r^2 = ε / (y+a) - ε^2 := Real.sq_sqrt hb.le
      have hrd : r < δ := by
        have hyp : 0 < y+a := by positivity
        have hquot : ε / (y+a) < δ^2 := by
          apply (div_lt_iff₀ hyp).2
          have haa : a * δ^2 = ε := by dsimp [a]; field_simp
          nlinarith [mul_pos hy (sq_pos_of_pos hδ)]
        nlinarith [sq_nonneg ε]
      have heq : {x : ℝ | (x-t)^2 < ε / (y+a) - ε^2} = Metric.ball t r := by
        ext x
        rw [Metric.mem_ball, Real.dist_eq]
        change (x-t)^2 < ε / (y+a) - ε^2 ↔ |x-t| < r
        rw [← hrs]
        simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (x-t)) hr.le)
      rw [heq]
      exact hballs r hr hrd
    · have heq : {x : ℝ | (x-t)^2 < ε / (y+a) - ε^2} = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro x hx
        exact hb (lt_of_le_of_lt (sq_nonneg (x-t)) hx)
      simp [heq]
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x) := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hfn) hfc.measurable.aemeasurable,
      lintegral_eq_lintegral_meas_lt volume (ae_of_all _ hfn) hfc.measurable.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hsuper y hy
  have hfi : (∫ x, f x ∂μ) ≤ c * ∫ x, f x := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfμ (ae_of_all _ hfn),
      ← ofReal_integral_eq_lintegral_ofReal hfv (ae_of_all _ hfn),
      ← ENNReal.ofReal_mul hc] at hlin
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlin
  have hmain : (∫ x, K x ∂μ) ≤ c * Real.pi + a * (μ univ).toReal := by
    calc
      (∫ x, K x ∂μ) ≤ ∫ x, f x + a ∂μ :=
        integral_mono hKμ (hfμ.add (integrable_const a)) (fun x => by
          have := le_max_left (K x-a) 0
          dsimp [f] at *
          linarith)
      _ = (∫ x, f x ∂μ) + a * (μ univ).toReal := by
        rw [integral_add hfμ (integrable_const a), integral_const, smul_eq_mul, mul_comm]
        rfl
      _ ≤ c * (∫ x, f x) + a * (μ univ).toReal := add_le_add hfi le_rfl
      _ ≤ c * Real.pi + a * (μ univ).toReal := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          ((integral_mono hfv hKv hfK).trans_eq hKi) hc) le_rfl
  rw [TeschlQM.Herglotz.borelTransform_im μ t ε hε]
  change (∫ x, K x ∂μ) / Real.pi ≤ _
  apply (div_le_iff₀ Real.pi_pos).2
  dsimp [a] at hmain
  calc
    (∫ x, K x ∂μ) ≤ c * Real.pi + (ε / δ^2) * (μ univ).toReal := hmain
    _ = (c + (ε / δ^2) * (μ univ).toReal / Real.pi) * Real.pi := by
      field_simp
