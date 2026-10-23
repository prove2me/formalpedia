-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.farField_trajectories
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:59:04.707254+00:00
-- url     : https://prove2.me/submissions/b8051ddc-e512-4fa4-8d5b-2c715c05d0bd

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace X6P42Far

noncomputable section

open Filter Set MeasureTheory

/-- The arccos antiderivative of the far-field integrand. -/
lemma hasDeriv_G (ρ s : ℝ) (hρ : 0 < ρ) (hs : ρ < s) :
    HasDerivAt (fun s => Real.arccos (ρ / s)) (ρ / (s ^ 2 * Real.sqrt (1 - (ρ / s) ^ 2))) s := by
  have hs0 : 0 < s := by linarith
  have hx1 : ρ / s < 1 := (div_lt_one hs0).2 hs
  have hx0 : 0 < ρ / s := div_pos hρ hs0
  have hinv : HasDerivAt (fun s : ℝ => ρ / s) (ρ * (-(s ^ 2)⁻¹)) s := by
    have := (hasDerivAt_inv hs0.ne').const_mul ρ
    simpa [div_eq_mul_inv] using this
  have h := (Real.hasDerivAt_arccos (x := ρ / s) (by linarith) hx1.ne).comp s hinv
  refine h.congr_deriv ?_
  have : 0 < 1 - (ρ / s) ^ 2 := by nlinarith
  have : 0 < Real.sqrt (1 - (ρ / s) ^ 2) := Real.sqrt_pos.2 this
  field_simp

lemma integral_main (A n ρ r : ℝ) (hn : 0 < n) (hρ : 0 < ρ) (hr : ρ ≤ r) :
    IntervalIntegrable (fun s => A / (s ^ 2 * Real.sqrt (n ^ 2 * (1 - (ρ / s) ^ 2)))) volume ρ r ∧
    (∫ s in ρ..r, A / (s ^ 2 * Real.sqrt (n ^ 2 * (1 - (ρ / s) ^ 2)))) =
      A / (n * ρ) * Real.arccos (ρ / r) := by
  set f := fun s : ℝ => A / (s ^ 2 * Real.sqrt (n ^ 2 * (1 - (ρ / s) ^ 2))) with hf
  set h := fun s : ℝ => ρ / (s ^ 2 * Real.sqrt (1 - (ρ / s) ^ 2)) with hh
  have hfh : ∀ s, 0 < s → f s = A / (n * ρ) * h s := by
    intro s hs
    simp only [hf, hh]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn.le]
    by_cases h0 : Real.sqrt (1 - (ρ / s) ^ 2) = 0
    · simp [h0]
    · field_simp
  have hcont : ContinuousOn (fun s => Real.arccos (ρ / s)) (Icc ρ r) := by
    apply Real.continuous_arccos.comp_continuousOn
    apply continuousOn_const.div continuousOn_id
    intro x hx; exact (lt_of_lt_of_le hρ hx.1).ne'
  have hderiv : ∀ x ∈ Ioo ρ r, HasDerivAt (fun s => Real.arccos (ρ / s)) (h x) x :=
    fun x hx => hasDeriv_G ρ x hρ hx.1
  have hint_h : IntegrableOn h (Ioc ρ r) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv (fun x hx => by
      have : 0 < x := by linarith [hx.1]
      simp only [hh]; positivity)
  have hint_f : IntegrableOn f (Ioc ρ r) := by
    have h2 : IntegrableOn (fun x => A / (n * ρ) * h x) (Ioc ρ r) := hint_h.const_mul _
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioc
    exact (hfh x (by linarith [hx.1])).symm
  have hII : IntervalIntegrable f volume ρ r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).2 hint_f
  refine ⟨hII, ?_⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr
    (continuousOn_const.mul hcont) (fun x hx => by
      have := (hderiv x hx).const_mul (A / (n * ρ))
      exact this.congr_deriv (hfh x (by linarith [hx.1])).symm) hII
  rw [this]
  simp [div_self hρ.ne']

lemma sin_slope (K : ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * Real.sin (K * Real.arcsin t)) (nhdsWithin 0 {0}ᶜ) (nhds K) := by
  have hd : HasDerivAt (fun t => Real.sin (K * Real.arcsin t)) K 0 := by
    have h1 := Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    have h2 := (h1.const_mul K).sin
    convert h2 using 1
    simp
  have := hd.tendsto_slope_zero
  simpa using this

end

end X6P42Far

open QAlgorithms.Papers.Independent.Renew46.P42 X6P42Far Filter Set MeasureTheory

theorem solution (c n W l phiBase : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W)
    (hl : angularAB c n W l ≠ 0)
    (hradicand : 0 < (angularAB c n W l) ^ 2 / n ^ 2 - (n ^ 2 - 1) * W ^ 2 / c ^ 2) :
    (∀ r : ℝ, farTurningRadius c n W l ≤ r →
      IntervalIntegrable (fun s => angularAB c n W l / (s ^ 2 * Real.sqrt (farRadial c n W l s)))
        volume (farTurningRadius c n W l) r ∧
      (∫ s in (farTurningRadius c n W l)..r,
        angularAB c n W l / (s ^ 2 * Real.sqrt (farRadial c n W l s))) =
          farAngle c n W l phiBase r - phiBase) ∧
    Tendsto (farAngle c n W l phiBase) atTop
      (nhds (phiBase + Real.pi * angularAB c n W l / (2 * n * farTurningRadius c n W l))) ∧
    Tendsto (fun r => r * Real.sin (farAngle c n W l phiBase r -
      (phiBase + Real.pi * angularAB c n W l / (2 * n * farTurningRadius c n W l))))
      atTop (nhds (-angularAB c n W l / n)) ∧
    (∀ r : ℝ, |angularAB c n W l| / n ≤ r →
      r * Real.cos ((angularAB c n W l / |angularAB c n W l|) *
        Real.arccos (|angularAB c n W l| / (n * r))) = |angularAB c n W l| / n) := by
  have hn0 : 0 < n := by linarith
  set A := angularAB c n W l with hA
  set ρ := farTurningRadius c n W l with hρ_def
  have hρ : 0 < ρ := Real.sqrt_pos.2 hradicand
  have hρ2 : ρ ^ 2 = A ^ 2 / n ^ 2 - (n ^ 2 - 1) * W ^ 2 / c ^ 2 := Real.sq_sqrt hradicand.le
  have hrad : ∀ s, s ≠ 0 → farRadial c n W l s = n ^ 2 * (1 - (ρ / s) ^ 2) := by
    intro s hs
    rw [farRadial, ← hA, div_pow, hρ2]
    field_simp
    ring
  have hfun : (fun s => A / (s ^ 2 * Real.sqrt (farRadial c n W l s))) =
      fun s => A / (s ^ 2 * Real.sqrt (n ^ 2 * (1 - (ρ / s) ^ 2))) := by
    funext s
    by_cases hs : s = 0
    · simp [hs]
    · rw [hrad s hs]
  have hangle : ∀ r, farAngle c n W l phiBase r = phiBase + A / (n * ρ) * Real.arccos (ρ / r) := by
    intro r; rfl
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hfun, hangle]
    obtain ⟨h1, h2⟩ := integral_main A n ρ r hn0 hρ hr
    exact ⟨h1, by rw [h2]; ring⟩
  · have hlim : Tendsto (fun r : ℝ => ρ / r) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := ((Real.continuous_arccos.tendsto 0).comp hlim).const_mul (A / (n * ρ)) |>.const_add phiBase
    rw [Real.arccos_zero] at this
    have e : phiBase + A / (n * ρ) * (Real.pi / 2) = phiBase + Real.pi * A / (2 * n * ρ) := by
      field_simp
    rw [e] at this
    refine this.congr (fun r => ?_)
    simp [hangle]
  · have hlim : Tendsto (fun r : ℝ => ρ / r) atTop (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with r hr
      exact (div_pos hρ hr).ne'
    have := ((sin_slope (A / (n * ρ))).comp hlim).const_mul (-ρ)
    have e : -ρ * (A / (n * ρ)) = -A / n := by field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    simp only [Function.comp, hangle]
    have : phiBase + A / (n * ρ) * Real.arccos (ρ / r) - (phiBase + Real.pi * A / (2 * n * ρ)) =
        -(A / (n * ρ) * Real.arcsin (ρ / r)) := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]; field_simp; ring
    rw [this, Real.sin_neg]
    field_simp
  · intro r hr
    have hA0 : 0 < |A| := abs_pos.2 hl
    have hr0 : 0 < r := lt_of_lt_of_le (div_pos hA0 hn0) hr
    have hx1 : |A| / (n * r) ≤ 1 := by
      rw [div_le_one (by positivity)]
      rw [div_le_iff₀ hn0] at hr; linarith
    have hx0 : -1 ≤ |A| / (n * r) := by
      have : 0 ≤ |A| / (n * r) := by positivity
      linarith
    have hcos : Real.cos (A / |A| * Real.arccos (|A| / (n * r))) = |A| / (n * r) := by
      rcases lt_or_gt_of_ne hl with h | h
      · rw [abs_of_neg h, div_neg, div_self h.ne, ← abs_of_neg h]
        rw [neg_mul, one_mul, Real.cos_neg, Real.cos_arccos hx0 hx1]
      · rw [abs_of_pos h, div_self h.ne', ← abs_of_pos h, one_mul, Real.cos_arccos hx0 hx1]
    rw [hcos]
    field_simp
