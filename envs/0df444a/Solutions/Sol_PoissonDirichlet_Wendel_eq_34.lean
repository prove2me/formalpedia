-- Prove2me | solution 1 for PoissonDirichlet.Wendel.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:39:20.333977+00:00
-- url     : https://prove2.me/submissions/946b3894-a2c0-4a2e-85bf-831bb372fd38

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.Wendel

open Set

/-- `x ^ (-a)` is integrable on `Ioc 0 1` for `a < 1`. -/
lemma w34_int_rpow_Ioc (a : ℝ) (ha1 : a < 1) :
    IntegrableOn (fun x : ℝ => x ^ (-a)) (Ioc (0:ℝ) 1) := by
  have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -a) (by linarith)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this

lemma w34_meas (a l : ℝ) :
    Measurable (fun x : ℝ => (1 - Real.exp (-l * x)) * x ^ (-a - 1)) := by
  fun_prop

lemma w34_meas2 (a l : ℝ) :
    Measurable (fun x : ℝ => Real.exp (-l * x) * x ^ (-a - 1)) := by
  fun_prop

lemma w34_meas3 (a l : ℝ) :
    Measurable (fun x : ℝ => x ^ (-a) * Real.exp (-l * x)) := by
  fun_prop

/-- `1 - exp(-l x) ≤ l x`. -/
lemma w34_one_sub_exp_le (l x : ℝ) : 1 - Real.exp (-l * x) ≤ l * x := by
  have := Real.add_one_le_exp (-l * x)
  linarith

lemma w34_one_sub_exp_nonneg (l x : ℝ) (hl : 0 ≤ l) (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-l * x) := by
  have : Real.exp (-l * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  linarith

/-- Integrability of `(1 - e^{-lx}) x^{-a-1}` on `Ioc 0 1`. -/
lemma w34_intA_Ioc (a l : ℝ) (ha : 0 < a) (ha1 : a < 1) (hl : 0 ≤ l) :
    IntegrableOn (fun x : ℝ => (1 - Real.exp (-l * x)) * x ^ (-a - 1)) (Ioc (0:ℝ) 1) := by
  have hg : IntegrableOn (fun x : ℝ => l * x ^ (-a)) (Ioc (0:ℝ) 1) :=
    (w34_int_rpow_Ioc a ha1).const_mul l
  refine Integrable.mono' hg (w34_meas a l).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
  have hx0 : 0 < x := hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (w34_one_sub_exp_nonneg l x hl hx0.le)
    (Real.rpow_nonneg hx0.le _))]
  have h1 : 1 - Real.exp (-l * x) ≤ l * x := w34_one_sub_exp_le l x
  have h2 : x ^ (-a) = x * x ^ (-a - 1) := by
    rw [show -a = (-a - 1) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]; ring
  rw [h2]
  have h3 : 0 ≤ x ^ (-a - 1) := Real.rpow_nonneg hx0.le _
  calc (1 - Real.exp (-l * x)) * x ^ (-a - 1) ≤ (l * x) * x ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = l * (x * x ^ (-a - 1)) := by ring

/-- Integrability of `e^{-lx} x^{-a-1}` on `Ioi 1`. -/
lemma w34_intB_Ioi (a l : ℝ) (ha : 0 < a) (hl : 0 ≤ l) :
    IntegrableOn (fun x : ℝ => Real.exp (-l * x) * x ^ (-a - 1)) (Ioi (1:ℝ)) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-a - 1)) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine Integrable.mono' hg (w34_meas2 a l).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
  have hx0 : 0 < x := lt_trans one_pos hx
  have h3 : 0 ≤ x ^ (-a - 1) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h3)]
  have : Real.exp (-l * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  calc Real.exp (-l * x) * x ^ (-a - 1) ≤ 1 * x ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right this h3
    _ = x ^ (-a - 1) := one_mul _

/-- Integrability of `(1 - e^{-lx}) x^{-a-1}` on `Ioi 1`. -/
lemma w34_intA_Ioi (a l : ℝ) (ha : 0 < a) (hl : 0 ≤ l) :
    IntegrableOn (fun x : ℝ => (1 - Real.exp (-l * x)) * x ^ (-a - 1)) (Ioi (1:ℝ)) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (-a - 1)) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine Integrable.mono' hg (w34_meas a l).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
  have hx0 : 0 < x := lt_trans one_pos hx
  have h3 : 0 ≤ x ^ (-a - 1) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (w34_one_sub_exp_nonneg l x hl hx0.le) h3)]
  have : 1 - Real.exp (-l * x) ≤ 1 := by linarith [Real.exp_pos (-l * x)]
  calc (1 - Real.exp (-l * x)) * x ^ (-a - 1) ≤ 1 * x ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right this h3
    _ = x ^ (-a - 1) := one_mul _

/-- Integrability of `x^{-a} e^{-lx}` on `Ioi 0`. -/
lemma w34_intC (a l : ℝ) (ha : 0 < a) (ha1 : a < 1) (hl : 0 < l) :
    IntegrableOn (fun x : ℝ => x ^ (-a) * Real.exp (-l * x)) (Ioi (0:ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · refine Integrable.mono' (w34_int_rpow_Ioc a ha1) (w34_meas3 a l).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have h3 : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (Real.exp_pos _).le)]
    have : Real.exp (-l * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc x ^ (-a) * Real.exp (-l * x) ≤ x ^ (-a) * 1 :=
          mul_le_mul_of_nonneg_left this h3
      _ = x ^ (-a) := mul_one _
  · have hg : IntegrableOn (fun x : ℝ => Real.exp (-l * x)) (Ioi (1:ℝ)) :=
      exp_neg_integrableOn_Ioi 1 hl
    refine Integrable.mono' hg (w34_meas3 a l).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx0 : 0 < x := lt_trans one_pos hx
    have h3 : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (Real.exp_pos _).le)]
    have : x ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    calc x ^ (-a) * Real.exp (-l * x) ≤ 1 * Real.exp (-l * x) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = Real.exp (-l * x) := one_mul _

/-- Key identity: `∫_0^∞ (1 - e^{-lx}) x^{-a-1} dx = Γ(1-a) l^a / a` for `l > 0`. -/
lemma w34_key (a l : ℝ) (ha : 0 < a) (ha1 : a < 1) (hl : 0 < l) :
    ∫ x in Ioi (0:ℝ), (1 - Real.exp (-l * x)) * x ^ (-a - 1) =
      Real.Gamma (1 - a) * l ^ a / a := by
  -- integration by parts with u = 1 - e^{-lx}, v = -x^{-a}/a
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun x => 1 - Real.exp (-l * x))
      (l * Real.exp (-l * x)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul (-l)).exp).const_sub 1
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun x : ℝ => -x ^ (-a) / a) (x ^ (-a - 1)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have h := ((Real.hasDerivAt_rpow_const (p := -a) (Or.inl hx0.ne')).neg).div_const a
    have e : -(-a * x ^ (-a - 1)) / a = x ^ (-a - 1) := by field_simp
    exact h.congr_deriv e
  have huv' : IntegrableOn ((fun x => 1 - Real.exp (-l * x)) * fun x : ℝ => x ^ (-a - 1))
      (Ioi (0:ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
    exact ⟨w34_intA_Ioc a l ha ha1 hl.le, w34_intA_Ioi a l ha hl.le⟩
  have hu'v : IntegrableOn ((fun x => l * Real.exp (-l * x)) * fun x : ℝ => -x ^ (-a) / a)
      (Ioi (0:ℝ)) := by
    have := (w34_intC a l ha ha1 hl).const_mul (-l / a)
    refine IntegrableOn.congr_fun this ?_ measurableSet_Ioi
    intro x _
    simp only [Pi.mul_apply]
    field_simp
  have h_zero : Tendsto ((fun x => 1 - Real.exp (-l * x)) * fun x : ℝ => -x ^ (-a) / a)
      (𝓝[>] 0) (𝓝 0) := by
    -- squeeze: -(l/a) x^{1-a} ≤ u v ≤ 0
    have hlim : Tendsto (fun x : ℝ => -(l / a) * x ^ (1 - a)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x ^ (1 - a)) (𝓝 0) (𝓝 ((0:ℝ) ^ (1 - a))) :=
        (Real.continuousAt_rpow_const 0 (1 - a) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at h1
      have := (h1.const_mul (-(l / a))).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (0:ℝ) < x := hx
      simp only [Pi.mul_apply]
      have h1 : 1 - Real.exp (-l * x) ≤ l * x := w34_one_sub_exp_le l x
      have h2 : x ^ (1 - a) = x * x ^ (-a) := by
        rw [show 1 - a = (-a) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]; ring
      have h3 : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
      rw [h2]
      have : (1 - Real.exp (-l * x)) * x ^ (-a) ≤ (l * x) * x ^ (-a) :=
        mul_le_mul_of_nonneg_right h1 h3
      have ha' : 0 < a := ha
      calc -(l / a) * (x * x ^ (-a)) = -(((l * x) * x ^ (-a)) / a) := by ring
        _ ≤ -(((1 - Real.exp (-l * x)) * x ^ (-a)) / a) := by
            apply neg_le_neg; exact div_le_div_of_nonneg_right this ha'.le
        _ = (1 - Real.exp (-l * x)) * (-x ^ (-a) / a) := by ring
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (0:ℝ) < x := hx
      simp only [Pi.mul_apply]
      have h3 : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
      have h4 := w34_one_sub_exp_nonneg l x hl.le hx0.le
      have : 0 ≤ (1 - Real.exp (-l * x)) * (x ^ (-a) / a) := by positivity
      linarith [show (1 - Real.exp (-l * x)) * (-x ^ (-a) / a) =
        -((1 - Real.exp (-l * x)) * (x ^ (-a) / a)) by ring]
  have h_infty : Tendsto ((fun x => 1 - Real.exp (-l * x)) * fun x : ℝ => -x ^ (-a) / a)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 - Real.exp (-l * x)) atTop (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
      refine this.congr fun x => ?_
      simp [Function.comp]
    have h2 : Tendsto (fun x : ℝ => -x ^ (-a) / a) atTop (𝓝 (-0 / a)) :=
      (tendsto_rpow_neg_atTop ha).neg.div_const a
    have := h1.mul h2
    rw [show ((fun x => 1 - Real.exp (-l * x)) * fun x : ℝ => -x ^ (-a) / a) =
      fun x => (1 - Real.exp (-l * x)) * (-x ^ (-a) / a) from rfl]
    simpa using this
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [key]
  have hI : ∫ x in Ioi (0:ℝ), l * Real.exp (-l * x) * (-x ^ (-a) / a) =
      (-l / a) * ∫ x in Ioi (0:ℝ), x ^ ((1 - a) - 1) * Real.exp (-(l * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show (1 - a) - 1 = -a by ring, show -(l * x) = -l * x by ring]
    field_simp
  rw [hI, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hl]
  have hl0 : l ≠ 0 := hl.ne'
  have : (1 / l) ^ (1 - a) = l ^ a / l := by
    rw [one_div, Real.inv_rpow hl.le, ← Real.rpow_neg hl.le, show -(1 - a) = a - 1 by ring,
      Real.rpow_sub_one hl0]
  rw [this]
  field_simp
  ring

/-- (34): `ψ_α(λ) = Γ(1 - α) λ^α + φ_α(λ)`. -/
theorem eq_34_core (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (l : ℝ) (hl : 0 ≤ l) :
    psi α l = Real.Gamma (1 - α) * l ^ α + phi α l := by
  unfold psi phi
  have hJ : ∫ x in Ioi (1:ℝ), x ^ (-α - 1) = 1 / α := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -α - 1 + 1 = -α by ring]
    field_simp
  rcases hl.lt_or_eq with hl | hl
  · have hsplit := setIntegral_union (f := fun x : ℝ => (1 - Real.exp (-l * x)) * x ^ (-α - 1))
      (μ := volume) (Ioc_disjoint_Ioi_same (a := (0:ℝ)) (b := 1)) measurableSet_Ioi
      (w34_intA_Ioc α l hα hα1 hl.le) (w34_intA_Ioi α l hα hl.le)
    rw [Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), w34_key α l hα hα1 hl] at hsplit
    have hB : ∫ x in Ioi (1:ℝ), (1 - Real.exp (-l * x)) * x ^ (-α - 1) =
        1 / α - ∫ x in Ioi (1:ℝ), Real.exp (-l * x) * x ^ (-α - 1) := by
      rw [← hJ, ← integral_sub (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
        (w34_intB_Ioi α l hα hl.le)]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      ring
    rw [hB] at hsplit
    have hα0 : α ≠ 0 := hα.ne'
    have : ∫ x in Ioc (0:ℝ) 1, (1 - Real.exp (-l * x)) * x ^ (-α - 1) =
        Real.Gamma (1 - α) * l ^ α / α - 1 / α +
          ∫ x in Ioi (1:ℝ), Real.exp (-l * x) * x ^ (-α - 1) := by linarith
    rw [this]
    field_simp
    ring
  · subst hl
    simp only [neg_zero, zero_mul, Real.exp_zero, sub_self, one_mul, integral_zero, mul_zero,
      add_zero]
    rw [Real.zero_rpow hα.ne', mul_zero, zero_add, hJ]
    field_simp

end PoissonDirichlet.Wendel

open PoissonDirichlet.Wendel


theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (l : ℝ) (hl : 0 ≤ l) :
    psi α l = Real.Gamma (1 - α) * l ^ α + phi α l := by
  exact eq_34_core α hα hα1 l hl
