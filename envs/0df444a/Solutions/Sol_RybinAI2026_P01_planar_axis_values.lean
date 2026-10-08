-- Prove2me | solution 1 for RybinAI2026.P01.planar_axis_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T15:21:13.403995+00:00
-- url     : https://prove2.me/submissions/744c182a-c023-4f45-aa75-f49c042d2d8a

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

theorem solution (m1 m2 : ℝ) (h1 : 0 < m1) (h2 : 0 < m2) :
    (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.cos (p - 0)| / (m1*(Real.cos p)^2 + m2*(Real.sin p)^2))
      = 4 * (∫ t in (0:ℝ)..1, (m1 + (m2-m1)*t^2)⁻¹) ∧
    (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.cos (p - Real.pi/2)| / (m1*(Real.cos p)^2 + m2*(Real.sin p)^2))
      = 4 * (∫ t in (0:ℝ)..1, (m2 + (m1-m2)*t^2)⁻¹) := by
  set q : ℝ → ℝ := fun p => m1 * (Real.cos p)^2 + m2 * (Real.sin p)^2 with hq
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hsc : ∀ p : ℝ, (Real.cos p)^2 + (Real.sin p)^2 = 1 := by
    intro p
    have h := Real.sin_sq_add_cos_sq p
    linarith
  have hqpos : ∀ p : ℝ, 0 < q p := by
    intro p
    rcases le_total m1 m2 with hle | hle
    · have hc2 : (Real.cos p)^2 = 1 - (Real.sin p)^2 := by
        linear_combination Real.sin_sq_add_cos_sq p
      have e : q p - m1 = (m2 - m1) * (Real.sin p)^2 := by
        simp only [hq]
        rw [hc2]
        ring
      have hnn : (0:ℝ) ≤ (m2 - m1) * (Real.sin p)^2 :=
        mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg _)
      linarith
    · have hss : (Real.sin p)^2 = 1 - (Real.cos p)^2 := by
        linear_combination Real.sin_sq_add_cos_sq p
      have e : q p - m2 = (m1 - m2) * (Real.cos p)^2 := by
        simp only [hq]
        rw [hss]
        ring
      have hnn : (0:ℝ) ≤ (m1 - m2) * (Real.cos p)^2 :=
        mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg _)
      linarith
  have hqC : Continuous q := by
    simp only [hq]
    exact (Continuous.mul continuous_const (Real.continuous_cos.pow 2)).add
      (Continuous.mul continuous_const (Real.continuous_sin.pow 2))
  have hF1C : Continuous (fun p : ℝ => |Real.cos p| / q p) := by
    have habs : Continuous (fun p : ℝ => ‖Real.cos p‖) :=
      continuous_norm.comp Real.continuous_cos
    simp only [← Real.norm_eq_abs]
    exact Continuous.div habs hqC (fun x => ne_of_gt (hqpos x))
  have hF2C : Continuous (fun p : ℝ => |Real.sin p| / q p) := by
    have habs : Continuous (fun p : ℝ => ‖Real.sin p‖) :=
      continuous_norm.comp Real.continuous_sin
    simp only [← Real.norm_eq_abs]
    exact Continuous.div habs hqC (fun x => ne_of_gt (hqpos x))
  have hint1 : ∀ a b : ℝ, IntervalIntegrable (fun p : ℝ => |Real.cos p| / q p) volume a b :=
    fun a b => (hF1C.continuousOn).intervalIntegrable
  have hint2 : ∀ a b : ℝ, IntervalIntegrable (fun p : ℝ => |Real.sin p| / q p) volume a b :=
    fun a b => (hF2C.continuousOn).intervalIntegrable
  -- First conjunct: psi = 0.
  have hper1 : ∀ x : ℝ, |Real.cos (x + Real.pi)| / q (x + Real.pi)
      = |Real.cos x| / q x := by
    intro x
    have eD : m1 * (-Real.cos x)^2 + m2 * (-Real.sin x)^2
        = m1 * (Real.cos x)^2 + m2 * (Real.sin x)^2 := by ring
    simp only [hq]
    rw [Real.cos_add_pi, Real.sin_add_pi, abs_neg, eD]
  have hrefl1pt : ∀ x : ℝ, |Real.cos (Real.pi - x)| / q (Real.pi - x)
      = |Real.cos x| / q x := by
    intro x
    have eD : m1 * (-Real.cos x)^2 + m2 * (Real.sin x)^2
        = m1 * (Real.cos x)^2 + m2 * (Real.sin x)^2 := by ring
    simp only [hq]
    rw [Real.cos_pi_sub, Real.sin_pi_sub, abs_neg, eD]
  have hsplit1 : (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.cos p| / q p)
      = (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.cos p| / q p)
        + ∫ p : ℝ in Real.pi..2*Real.pi, |Real.cos p| / q p :=
    (integral_add_adjacent_intervals (hint1 0 Real.pi) (hint1 Real.pi (2*Real.pi))).symm
  have hshift1 : (∫ p : ℝ in Real.pi..2*Real.pi, |Real.cos p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi, |Real.cos p| / q p := by
    have hbase := integral_comp_add_right
      (f := fun p : ℝ => |Real.cos p| / q p) (a := (0:ℝ)) (b := Real.pi) (d := Real.pi)
    have e0 : (0:ℝ) + Real.pi = Real.pi := zero_add _
    have e2 : Real.pi + Real.pi = 2 * Real.pi := by ring
    rw [e0, e2] at hbase
    simp only [hper1] at hbase
    exact hbase.symm
  have hsplit2 : (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.cos p| / q p)
      = (∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.cos p| / q p)
        + ∫ p : ℝ in (Real.pi/2)..Real.pi, |Real.cos p| / q p :=
    (integral_add_adjacent_intervals (hint1 0 (Real.pi/2)) (hint1 (Real.pi/2) Real.pi)).symm
  have hrefl1 : (∫ p : ℝ in (Real.pi/2)..Real.pi, |Real.cos p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.cos p| / q p := by
    have hbase := integral_comp_sub_left
      (f := fun p : ℝ => |Real.cos p| / q p) (a := Real.pi/2) (b := Real.pi) (d := Real.pi)
    have e0 : Real.pi - Real.pi = (0:ℝ) := sub_self _
    have e1 : Real.pi - Real.pi/2 = Real.pi/2 := by ring
    rw [e0, e1] at hbase
    simp only [hrefl1pt] at hbase
    exact hbase
  have habs1 : ∀ p ∈ Set.uIcc (0:ℝ) (Real.pi/2), |Real.cos p| / q p
      = Real.cos p / q p := by
    intro p hp
    have h01 : (0:ℝ) ≤ Real.pi/2 := by linarith [Real.pi_pos]
    rw [Set.uIcc_of_le h01, Set.mem_Icc] at hp
    have hnn : 0 ≤ Real.cos p :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hp.1, Real.pi_pos], hp.2⟩
    rw [abs_of_nonneg hnn]
  have hcongr1 : (∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.cos p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi/2, Real.cos p / q p := by
    apply integral_congr
    intro p hp
    exact habs1 p hp
  have hbridge1 : ∀ p ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      Real.cos p / q p
        = ((fun t : ℝ => (m1 + (m2-m1)*t^2)⁻¹) ∘ Real.sin) p * Real.cos p := by
    intro p hp
    have hc2 : (Real.cos p)^2 = 1 - (Real.sin p)^2 := by
      linear_combination Real.sin_sq_add_cos_sq p
    have hqq : q p = m1 + (m2-m1)*(Real.sin p)^2 := by
      simp only [hq]
      rw [hc2]
      ring
    simp only [Function.comp_apply]
    rw [hqq, div_eq_mul_inv]
    ring
  have hcongr1b : (∫ p : ℝ in (0:ℝ)..Real.pi/2, Real.cos p / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi/2,
        ((fun t : ℝ => (m1 + (m2-m1)*t^2)⁻¹) ∘ Real.sin) p * Real.cos p := by
    apply integral_congr
    intro p hp
    exact hbridge1 p hp
  have hsubst1 := integral_comp_mul_deriv_of_deriv_nonneg
    (f := Real.sin) (f' := Real.cos)
    (g := fun t : ℝ => (m1 + (m2-m1)*t^2)⁻¹)
    (a := (0:ℝ)) (b := Real.pi/2)
    Real.continuous_sin.continuousOn
    (fun x _ => Real.hasDerivAt_sin x)
    (fun x hx => by
      rw [Set.mem_Ioo] at hx
      have h1 : -(Real.pi/2) ≤ x := by
        have hm : -(Real.pi/2) ≤ min (0:ℝ) (Real.pi/2) :=
          le_min (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        linarith [hx.1, hm]
      have h2 : x ≤ Real.pi/2 := by
        have hM : max (0:ℝ) (Real.pi/2) ≤ Real.pi/2 :=
          max_le (by linarith [Real.pi_pos]) le_rfl
        linarith [hx.2, hM]
      exact Real.cos_nonneg_of_mem_Icc ⟨h1, h2⟩)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsubst1
  beta_reduce at hsubst1
  have hfin1 : (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.cos p| / q p)
      = 2 * (∫ t in (0:ℝ)..1, (m1 + (m2-m1)*t^2)⁻¹) := by
    rw [hsplit2, hrefl1, hcongr1, hcongr1b, hsubst1]
    ring
  have htot1 : (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.cos p| / q p)
      = 4 * (∫ t in (0:ℝ)..1, (m1 + (m2-m1)*t^2)⁻¹) := by
    rw [hsplit1, hshift1, hfin1]
    ring
  -- Second conjunct: psi = pi/2.
  have hper2 : ∀ x : ℝ, |Real.sin (x + Real.pi)| / q (x + Real.pi)
      = |Real.sin x| / q x := by
    intro x
    have eD : m1 * (-Real.cos x)^2 + m2 * (-Real.sin x)^2
        = m1 * (Real.cos x)^2 + m2 * (Real.sin x)^2 := by ring
    simp only [hq]
    rw [Real.sin_add_pi, Real.cos_add_pi, abs_neg, eD]
  have hrefl2pt : ∀ x : ℝ, |Real.sin (Real.pi - x)| / q (Real.pi - x)
      = |Real.sin x| / q x := by
    intro x
    have eD : m1 * (-Real.cos x)^2 + m2 * (Real.sin x)^2
        = m1 * (Real.cos x)^2 + m2 * (Real.sin x)^2 := by ring
    simp only [hq]
    rw [Real.sin_pi_sub, Real.cos_pi_sub, eD]
  have hsplit1' : (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.sin p| / q p)
      = (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.sin p| / q p)
        + ∫ p : ℝ in Real.pi..2*Real.pi, |Real.sin p| / q p :=
    (integral_add_adjacent_intervals (hint2 0 Real.pi) (hint2 Real.pi (2*Real.pi))).symm
  have hshift1' : (∫ p : ℝ in Real.pi..2*Real.pi, |Real.sin p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi, |Real.sin p| / q p := by
    have hbase := integral_comp_add_right
      (f := fun p : ℝ => |Real.sin p| / q p) (a := (0:ℝ)) (b := Real.pi) (d := Real.pi)
    have e0 : (0:ℝ) + Real.pi = Real.pi := zero_add _
    have e2 : Real.pi + Real.pi = 2 * Real.pi := by ring
    rw [e0, e2] at hbase
    simp only [hper2] at hbase
    exact hbase.symm
  have hsplit2' : (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.sin p| / q p)
      = (∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.sin p| / q p)
        + ∫ p : ℝ in (Real.pi/2)..Real.pi, |Real.sin p| / q p :=
    (integral_add_adjacent_intervals (hint2 0 (Real.pi/2)) (hint2 (Real.pi/2) Real.pi)).symm
  have hrefl1' : (∫ p : ℝ in (Real.pi/2)..Real.pi, |Real.sin p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.sin p| / q p := by
    have hbase := integral_comp_sub_left
      (f := fun p : ℝ => |Real.sin p| / q p) (a := Real.pi/2) (b := Real.pi) (d := Real.pi)
    have e0 : Real.pi - Real.pi = (0:ℝ) := sub_self _
    have e1 : Real.pi - Real.pi/2 = Real.pi/2 := by ring
    rw [e0, e1] at hbase
    simp only [hrefl2pt] at hbase
    exact hbase
  have habs2 : ∀ p ∈ Set.uIcc (0:ℝ) (Real.pi/2), |Real.sin p| / q p
      = Real.sin p / q p := by
    intro p hp
    have h01 : (0:ℝ) ≤ Real.pi/2 := by linarith [Real.pi_pos]
    rw [Set.uIcc_of_le h01, Set.mem_Icc] at hp
    have hnn : 0 ≤ Real.sin p :=
      Real.sin_nonneg_of_mem_Icc ⟨hp.1, le_trans hp.2 (by linarith [Real.pi_pos])⟩
    rw [abs_of_nonneg hnn]
  have hcongr2a : (∫ p : ℝ in (0:ℝ)..Real.pi/2, |Real.sin p| / q p)
      = ∫ p : ℝ in (0:ℝ)..Real.pi/2, Real.sin p / q p := by
    apply integral_congr
    intro p hp
    exact habs2 p hp
  have hbridge2 : ∀ p ∈ Set.uIcc (0:ℝ) (Real.pi/2),
      Real.sin p / q p
        = -(((fun t : ℝ => (m2 + (m1-m2)*t^2)⁻¹) ∘ Real.cos) p
          * ((fun x : ℝ => -Real.sin x) p)) := by
    intro p hp
    have hss : (Real.sin p)^2 = 1 - (Real.cos p)^2 := by
      linear_combination Real.sin_sq_add_cos_sq p
    have hqq : q p = m2 + (m1-m2)*(Real.cos p)^2 := by
      simp only [hq]
      rw [hss]
      ring
    simp only [Function.comp_apply]
    rw [hqq, div_eq_mul_inv]
    ring
  have hcongr2b : (∫ p : ℝ in (0:ℝ)..Real.pi/2, Real.sin p / q p)
      = -(∫ p : ℝ in (0:ℝ)..Real.pi/2,
        ((fun t : ℝ => (m2 + (m1-m2)*t^2)⁻¹) ∘ Real.cos) p
          * ((fun x : ℝ => -Real.sin x) p)) := by
    rw [← intervalIntegral.integral_neg]
    apply integral_congr
    intro p hp
    exact hbridge2 p hp
  have hsubst2 := integral_comp_mul_deriv_of_deriv_nonpos
    (f := Real.cos) (f' := fun x : ℝ => -Real.sin x)
    (g := fun t : ℝ => (m2 + (m1-m2)*t^2)⁻¹)
    (a := (0:ℝ)) (b := Real.pi/2)
    Real.continuous_cos.continuousOn
    (fun x _ => Real.hasDerivAt_cos x)
    (fun x hx => by
      rw [Set.mem_Ioo] at hx
      have hlo : (0:ℝ) ≤ x := by
        have hm : (0:ℝ) ≤ min (0:ℝ) (Real.pi/2) :=
          le_min le_rfl (by linarith [Real.pi_pos])
        linarith [hx.1, hm]
      have hhi : x ≤ Real.pi := by
        have hM : max (0:ℝ) (Real.pi/2) ≤ Real.pi :=
          max_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        linarith [hx.2, hM]
      exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc ⟨hlo, hhi⟩))
  rw [Real.cos_zero, Real.cos_pi_div_two] at hsubst2
  conv at hsubst2 =>
    rhs
    rw [integral_symm]
  simp only [Function.comp_apply] at hsubst2
  beta_reduce at hsubst2
  have hQ2 : (∫ p : ℝ in (0:ℝ)..Real.pi/2, Real.sin p / q p)
      = ∫ t in (0:ℝ)..1, (m2 + (m1-m2)*t^2)⁻¹ := by
    rw [hcongr2b]
    simp only [Function.comp_apply]
    beta_reduce
    rw [hsubst2]
    simp only [neg_neg]
  have hfin2 : (∫ p : ℝ in (0:ℝ)..Real.pi, |Real.sin p| / q p)
      = 2 * (∫ t in (0:ℝ)..1, (m2 + (m1-m2)*t^2)⁻¹) := by
    rw [hsplit2', hrefl1', hcongr2a, hQ2]
    ring
  have htot2 : (∫ p : ℝ in (0:ℝ)..2*Real.pi, |Real.sin p| / q p)
      = 4 * (∫ t in (0:ℝ)..1, (m2 + (m1-m2)*t^2)⁻¹) := by
    rw [hsplit1', hshift1', hfin2]
    ring
  simp only [sub_zero]
  simp only [Real.cos_sub_pi_div_two]
  exact ⟨htot1, htot2⟩
