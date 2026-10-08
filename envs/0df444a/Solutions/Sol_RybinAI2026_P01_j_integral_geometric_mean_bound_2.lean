-- Prove2me | solution 2 for RybinAI2026.P01.j_integral_geometric_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T16:02:40.219085+00:00
-- url     : https://prove2.me/submissions/c480be81-e17a-4670-b6a9-8d55841db4e2

-- (Trigonometric/Arctan.lean); Real.sin_lt (h : 0 < x) : sin x < x (Trigonometric/Bounds.lean).

import Mathlib
import Theorems.Thm_RybinAI2026_P01_j_closed_pos
import Theorems.Thm_RybinAI2026_P01_j_closed_neg
set_option autoImplicit false
open MeasureTheory
open intervalIntegral
open RybinAI2026.P01

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b ≤ a → (∫ t in (0:ℝ)..1, (a + (b-a)*t^2)⁻¹) ≤ 1 / Real.sqrt (a*b)) ∧
    (a ≤ b → 1 / Real.sqrt (a*b) ≤ (∫ t in (0:ℝ)..1, (a + (b-a)*t^2)⁻¹)) := by
  have hane : a ≠ 0 := ha.ne'
  set j : ℝ → ℝ := fun c => ∫ t in (0:ℝ)..1, ((1:ℝ) + c*t^2)⁻¹ with hj
  have hJ : ∀ b : ℝ, 0 < b →
      (∫ t in (0:ℝ)..1, (a + (b-a)*t^2)⁻¹) = j ((b-a)/a) / a := by
    intro b hb
    have e : ∀ t : ℝ, ((a + (b-a)*t^2)⁻¹)
        = a⁻¹ * ((1 + ((b-a)/a)*t^2)⁻¹) := by
      intro t
      have e2 : a + (b-a)*t^2 = a * (1 + ((b-a)/a)*t^2) := by
        field_simp
      rw [e2, mul_inv_rev, mul_comm]
    simp only [e, intervalIntegral.integral_const_mul, hj, div_eq_mul_inv]
    ring
  have hdiag : (∫ t in (0:ℝ)..1, (a + (a-a)*t^2)⁻¹) = a⁻¹ := by
    have e : ∀ t : ℝ, (a + (a-a)*t^2)⁻¹ = a⁻¹ := by
      intro t
      congr 1
      ring
    simp only [e]
    rw [intervalIntegral.integral_const]
    simp
  constructor
  · intro hba
    rcases eq_or_lt_of_le hba with hbe | hblt
    · -- diagonal: b = a, both sides equal 1 / a
      subst hbe
      rw [hdiag, Real.sqrt_mul_self ha.le, one_div]
    · -- strict case b < a: artanh closed form
      have hc1 : (-1:ℝ) < (b-a)/a := by
        have hba2 : (0:ℝ) < b / a := div_pos hb ha
        rw [sub_div, div_self hane]
        linarith
      have hc0 : (b-a)/a < 0 := div_neg_of_neg_of_pos (by linarith) ha
      have hw0 : (0:ℝ) < Real.sqrt (-((b-a)/a)) :=
        Real.sqrt_pos.mpr (neg_pos.mpr hc0)
      have hw1 : Real.sqrt (-((b-a)/a)) < 1 := by
        have h := Real.sqrt_lt_sqrt (le_of_lt (neg_pos.mpr hc0))
          (show -((b-a)/a) < 1 by linarith)
        rwa [Real.sqrt_one] at h
      have hwsq : (Real.sqrt (-((b-a)/a)))^2 = (a-b)/a := by
        rw [Real.sq_sqrt (neg_pos.mpr hc0).le]
        ring
      have hspos : (0:ℝ) < 1 - (Real.sqrt (-((b-a)/a)))^2 := by
        have h2 : (Real.sqrt (-((b-a)/a)))^2 < 1 := by nlinarith [hw0, hw1]
        linarith
      -- scalar upper bound (only remaining obligation on this side)
      have key : Real.artanh (Real.sqrt (-((b-a)/a)))
          ≤ Real.sqrt (-((b-a)/a)) / Real.sqrt (1 - (Real.sqrt (-((b-a)/a)))^2) := by
        -- EVIDENCE (2026-10-05): numeric sweep on 999 pts of (0,1) gives
        -- min f = 1.7e-10, min f' = 5.0e-07, both ≥ 0; f(0.999) = 18.54.
        -- Proof via StrictMonoOn from positive derivative (mirrors accepted
        -- artanh_three_div_bound_v10 throughout).
        set w : ℝ := Real.sqrt (-((b-a)/a)) with hw
        have hwIcc : w ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, hw1.le⟩
        have eartw : Real.artanh w = (1/2) * Real.log ((1+w)/(1-w)) :=
          Real.artanh_eq_half_log hwIcc
        have hFder : ∀ x ∈ Set.Icc (0:ℝ) w, HasDerivAt
            (fun v => v / Real.sqrt (1 - v^2) - (1/2) * Real.log ((1+v)/(1-v)))
            (1/((1-x^2)*Real.sqrt (1-x^2)) - 1/(1-x^2)) x := by
          intro x hx
          rw [Set.mem_Icc] at hx
          have hx2 : x^2 < 1 := by
            nlinarith [hx.1, hx.2, hw0.le, hw1.le, sq_nonneg x, sq_nonneg w]
          have hx1 : (0:ℝ) < 1 - x^2 := by linarith
          have hsne : Real.sqrt (1 - x^2) ≠ 0 := (Real.sqrt_pos.mpr hx1).ne'
          have h1x2 : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt hx1
          have h1mw : (1:ℝ) - x ≠ 0 := ne_of_gt (by linarith [hx.2, hw1])
          have h1pw : (1:ℝ) + x ≠ 0 := ne_of_gt (by linarith [hx.1])
          have hsqw : (Real.sqrt (1-x^2))^2 = 1-x^2 := Real.sq_sqrt hx1.le
          have hinner : HasDerivAt (fun v : ℝ => 1 - v^2) (0 - 2*x) x := by
            have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
            have h2 : HasDerivAt (fun v : ℝ => v^2) (2*x) x := by
              have h := hasDerivAt_pow 2 x
              simpa using h
            exact h1.sub h2
          have hsq2 : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v^2))
              ((1/(2*Real.sqrt (1-x^2))) * (0 - 2*x)) x :=
            HasDerivAt.comp x (Real.hasDerivAt_sqrt (ne_of_gt hx1)) hinner
          have hg : HasDerivAt (fun v : ℝ => v / Real.sqrt (1 - v^2))
              (1/((1-x^2)*Real.sqrt (1-x^2))) x := by
            have hnum : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id' x
            have h := hnum.div hsq2 hsne
            have hval : (1 * Real.sqrt (1-x^2)
                - x * ((1/(2*Real.sqrt (1-x^2))) * (0 - 2*x)))
                / (Real.sqrt (1-x^2))^2
                = 1/((1-x^2)*Real.sqrt (1-x^2)) := by
              field_simp [hsqw]
              rw [hsqw]
              ring
            rwa [hval] at h
          have hN : HasDerivAt (fun v : ℝ => 1 + v) (0 + 1) x := by
            have ha1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
            have hb1 : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id' x
            exact ha1.add hb1
          have hD : HasDerivAt (fun v : ℝ => 1 - v) (0 - 1) x := by
            have ha1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
            have hb1 : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id' x
            exact ha1.sub hb1
          have hq := hN.div hD h1mw
          have hq2 : HasDerivAt (fun v : ℝ => (1+v)/(1-v)) (2/(1-x)^2) x := by
            have hbridge : (((0+1)*(1-x) - (1+x)*(0-1))/(1-x)^2) = 2/(1-x)^2 := by
              ring
            rwa [hbridge] at hq
          have hne2q : (1+x)/(1-x) ≠ 0 :=
            ne_of_gt (by apply div_pos <;> linarith [hx.1, hx.2, hw1])
          have hl := hq2.log hne2q
          have hL : HasDerivAt (fun v : ℝ => (1/2) * Real.log ((1+v)/(1-v)))
              (1/(1-x^2)) x := by
            have hc := HasDerivAt.const_mul (1 / 2) hl
            have hval : (1/2) * ((2/(1-x)^2)/((1+x)/(1-x))) = 1/(1-x^2) := by
              field_simp
              ring
            rwa [hval] at hc
          exact hg.sub hL
        have hFcont : ContinuousOn
            (fun v => v / Real.sqrt (1 - v^2) - (1/2) * Real.log ((1+v)/(1-v)))
            (Set.Icc 0 w) := by
          intro x hx
          exact (hFder x hx).continuousAt.continuousWithinAt
        have hderiv : ∀ x ∈ interior (Set.Icc (0:ℝ) w),
            0 < deriv (fun v => v / Real.sqrt (1 - v^2)
              - (1/2) * Real.log ((1+v)/(1-v))) x := by
          intro x hx
          rw [interior_Icc] at hx
          have hxI : x ∈ Set.Icc (0:ℝ) w := Set.Ioo_subset_Icc_self hx
          have hFx := hFder x hxI
          rw [hFx.deriv]
          have hs : (0:ℝ) < Real.sqrt (1-x^2) := by
            have hx1 : (0:ℝ) < 1 - x^2 := by
              have h2 : x^2 < 1 := by
                nlinarith [hx.1, hx.2, hw0.le, hw1.le, sq_nonneg x, sq_nonneg w]
              linarith
            exact Real.sqrt_pos.mpr hx1
          have hs1 : Real.sqrt (1-x^2) < 1 := by
            have h2 : x^2 < 1 := by
              nlinarith [hx.1, hx.2, hw0.le, hw1.le, sq_nonneg x, sq_nonneg w]
            have hle : (0:ℝ) ≤ 1 - x^2 := by linarith
            have hpos : (0:ℝ) < x^2 := pow_pos hx.1 2
            calc Real.sqrt (1-x^2) < Real.sqrt 1 :=
                  Real.sqrt_lt_sqrt (by linarith) (by linarith [hpos])
              _ = 1 := Real.sqrt_one
          have hA : (0:ℝ) < 1 - x^2 := by
            have h2 : x^2 < 1 := by
              nlinarith [hx.1, hx.2, hw0.le, hw1.le, sq_nonneg x, sq_nonneg w]
            linarith
          have hlt : 1/(1-x^2) < 1/((1-x^2)*Real.sqrt (1-x^2)) :=
            one_div_lt_one_div_of_lt (mul_pos hA hs) (by
              have hle := mul_lt_mul_of_pos_left hs1 hA
              simpa using hle)
          linarith
        have hmono : StrictMonoOn
            (fun v => v / Real.sqrt (1 - v^2) - (1/2) * Real.log ((1+v)/(1-v)))
            (Set.Icc 0 w) :=
          strictMonoOn_of_deriv_pos (convex_Icc 0 w) hFcont hderiv
        have h0mem : (0:ℝ) ∈ Set.Icc 0 w := ⟨le_rfl, hw0.le⟩
        have hwmem : w ∈ Set.Icc 0 w := ⟨hw0.le, le_rfl⟩
        have hlt := hmono h0mem hwmem hw0
        have hF0 : (fun v => v / Real.sqrt (1 - v^2)
            - (1/2) * Real.log ((1+v)/(1-v))) 0 = 0 := by simp
        rw [hF0] at hlt
        have hlt2 : (0:ℝ) < w / Real.sqrt (1-w^2) - (1/2)*Real.log ((1+w)/(1-w)) := hlt
        rw [← eartw] at hlt2
        linarith
      have hb_eq : b = a * (1 - (Real.sqrt (-((b-a)/a)))^2) := by
        have h1 : a * (Real.sqrt (-((b-a)/a)))^2 = a - b := by
          rw [hwsq]
          field_simp
        linarith
      have hsqrt_ab : Real.sqrt (a*b)
          = a * Real.sqrt (1 - (Real.sqrt (-((b-a)/a)))^2) := by
        have e : a * b = a^2 * (1 - (Real.sqrt (-((b-a)/a)))^2) := by
          conv_lhs => rw [hb_eq]
          ring
        rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      have e2 : (1:ℝ) / (a * Real.sqrt (1 - (Real.sqrt (-((b-a)/a)))^2))
          = ((Real.sqrt (-((b-a)/a)) / Real.sqrt (1 - (Real.sqrt (-((b-a)/a)))^2))
            / Real.sqrt (-((b-a)/a))) / a := by
        have hwne : Real.sqrt (-((b-a)/a)) ≠ 0 := hw0.ne'
        have hsne : Real.sqrt (1 - (Real.sqrt (-((b-a)/a)))^2) ≠ 0 :=
          (Real.sqrt_pos.mpr hspos).ne'
        field_simp
      have hjc : j ((b-a)/a)
          = Real.artanh (Real.sqrt (-((b-a)/a)))
            / Real.sqrt (-((b-a)/a)) :=
        j_closed_neg _ hc1 hc0
      rw [hJ b hb, hjc, hsqrt_ab, e2, div_le_div_iff_of_pos_right ha, div_le_div_iff_of_pos_right hw0]
      exact key
  · intro hab
    rcases eq_or_lt_of_le hab with hae | halt
    · -- diagonal: a = b
      subst hae
      rw [hdiag]
      have e : (1:ℝ) / Real.sqrt (a * a) = a⁻¹ := by
        rw [Real.sqrt_mul_self ha.le, one_div]
      rw [e]
    · -- strict case a < b: arctan closed form
      have hc : (0:ℝ) < (b-a)/a := div_pos (by linarith) ha
      have hs0 : (0:ℝ) < Real.sqrt ((b-a)/a) := Real.sqrt_pos.mpr hc
      have hssq : (Real.sqrt ((b-a)/a))^2 = (b-a)/a :=
        Real.sq_sqrt hc.le
      have key2 : Real.sqrt ((b-a)/a) / Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2)
          ≤ Real.arctan (Real.sqrt ((b-a)/a)) := by
        have hsin : Real.sin (Real.arctan (Real.sqrt ((b-a)/a)))
            = Real.sqrt ((b-a)/a) / Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2) :=
          Real.sin_arctan _
        have hlt : Real.sin (Real.arctan (Real.sqrt ((b-a)/a)))
            < Real.arctan (Real.sqrt ((b-a)/a)) :=
          Real.sin_lt (Real.arctan_pos.mpr hs0)
        rw [hsin] at hlt
        exact hlt.le
      have hb_eq : b = a * (1 + (Real.sqrt ((b-a)/a))^2) := by
        have h1 : a * (Real.sqrt ((b-a)/a))^2 = b - a := by
          rw [hssq]
          field_simp
        linarith
      have hsqrt_ab : Real.sqrt (a*b)
          = a * Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2) := by
        have e : a * b = a^2 * (1 + (Real.sqrt ((b-a)/a))^2) := by
          conv_lhs => rw [hb_eq]
          ring
        rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      have e2 : (1:ℝ) / (a * Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2))
          = ((Real.sqrt ((b-a)/a) / Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2))
            / Real.sqrt ((b-a)/a)) / a := by
        have hsne : Real.sqrt ((b-a)/a) ≠ 0 := hs0.ne'
        have h1s : (0:ℝ) < 1 + (Real.sqrt ((b-a)/a))^2 := by positivity
        have hs1ne : Real.sqrt (1 + (Real.sqrt ((b-a)/a))^2) ≠ 0 :=
          (Real.sqrt_pos.mpr h1s).ne'
        field_simp
      have hjc : j ((b-a)/a)
          = Real.arctan (Real.sqrt ((b-a)/a)) / Real.sqrt ((b-a)/a) :=
        j_closed_pos _ hc
      rw [hJ b hb, hjc, hsqrt_ab, e2, div_le_div_iff_of_pos_right ha, div_le_div_iff_of_pos_right hs0]
      exact key2
