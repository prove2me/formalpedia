-- Prove2me | solution 1 for StallEconomy.TripLength.second_moment_X
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:39:08.775799+00:00
-- url     : https://prove2.me/submissions/0bf5ba0e-b9c3-498d-9b96-c7ff67dacc34

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

set_option autoImplicit false
open MeasureTheory StallEconomy.TripLength

lemma stl2_zone_int (h : ℝ) (hh : 0 ≤ h) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ p in {p : ℝ × ℝ | |p.1| + |p.2| ≤ h}, g p.1 = ∫ x in (-h)..h, g x * (2 * (h - |x|)) := by
  set Z : Set (ℝ × ℝ) := {p | |p.1| + |p.2| ≤ h} with hZ
  have hZm : MeasurableSet Z := measurableSet_le (by fun_prop) measurable_const
  have hZc : IsCompact Z := by
    apply IsCompact.of_isClosed_subset
      ((isCompact_Icc (a := -h) (b := h)).prod (isCompact_Icc (a := -h) (b := h)))
    · exact isClosed_le (by fun_prop) continuous_const
    · intro p hp
      simp only [hZ, Set.mem_setOf_eq] at hp
      have h1 := abs_nonneg p.1
      have h2 := abs_nonneg p.2
      have h3 := abs_le.1 (show |p.1| ≤ h by linarith)
      have h4 := abs_le.1 (show |p.2| ≤ h by linarith)
      exact ⟨⟨h3.1, h3.2⟩, ⟨h4.1, h4.2⟩⟩
  have hint : IntegrableOn (fun p : ℝ × ℝ => g p.1) Z :=
    (hg.comp continuous_fst).continuousOn.integrableOn_compact hZc
  rw [← integral_indicator hZm]
  have hint2 : Integrable (Z.indicator (fun p : ℝ × ℝ => g p.1)) (volume : Measure (ℝ × ℝ)) :=
    (integrable_indicator_iff hZm).2 hint
  rw [Measure.volume_eq_prod] at hint2 ⊢
  rw [integral_prod _ hint2]
  have hinner : ∀ x : ℝ, ∫ y, Z.indicator (fun p : ℝ × ℝ => g p.1) (x, y) =
      g x * max (2 * (h - |x|)) 0 := by
    intro x
    have hy : ∀ y : ℝ, Z.indicator (fun p : ℝ × ℝ => g p.1) (x, y) =
        (Set.Icc (-(h - |x|)) (h - |x|)).indicator (fun _ => g x) y := by
      intro y
      by_cases hy : y ∈ Set.Icc (-(h - |x|)) (h - |x|)
      · have hm : (x, y) ∈ Z := by
          simp only [hZ, Set.mem_setOf_eq]
          have := abs_le.2 ⟨hy.1, hy.2⟩
          linarith
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem hy]
      · have hm : (x, y) ∉ Z := by
          intro hm
          apply hy
          simp only [hZ, Set.mem_setOf_eq] at hm
          have := abs_le.1 (show |y| ≤ h - |x| by linarith)
          exact ⟨this.1, this.2⟩
        rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hy]
    simp_rw [hy]
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
      show (h - |x|) - (-(h - |x|)) = 2 * (h - |x|) by ring]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  have hz : ∀ x : ℝ, x ∉ Set.Icc (-h) h → g x * max (2 * (h - |x|)) 0 = 0 := by
    intro x hx
    have : h < |x| := by
      by_contra hle
      push_neg at hle
      exact hx ⟨(abs_le.1 hle).1, (abs_le.1 hle).2⟩
    rw [max_eq_right (by linarith)]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  have : |x| ≤ h := abs_le.2 ⟨hx.1, hx.2⟩
  simp only
  rw [max_eq_left (by linarith)]

lemma stl2_fold (h : ℝ) (hh : 0 ≤ h) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ x in (-h)..h, φ x * (2 * (h - |x|)) = ∫ x in (0:ℝ)..h, (φ x + φ (-x)) * (2 * (h - x)) := by
  have hc : Continuous fun x : ℝ => φ x * (2 * (h - |x|)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (-h)..0, φ x * (2 * (h - |x|)) = ∫ x in (0:ℝ)..h, φ (-x) * (2 * (h - x)) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := h)
      (f := fun x : ℝ => φ x * (2 * (h - |x|)))
    simp only [abs_neg, neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hh] at hx
    simp only [abs_of_nonneg hx.1]
  have e2 : ∫ x in (0:ℝ)..h, φ x * (2 * (h - |x|)) = ∫ x in (0:ℝ)..h, φ x * (2 * (h - x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hh] at hx
    simp only [abs_of_nonneg hx.1]
  have i1 : IntervalIntegrable (fun x : ℝ => φ (-x) * (2 * (h - x))) volume 0 h :=
    (by fun_prop : Continuous fun x : ℝ => φ (-x) * (2 * (h - x))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => φ x * (2 * (h - x))) volume 0 h :=
    (by fun_prop : Continuous fun x : ℝ => φ x * (2 * (h - x))).intervalIntegrable _ _
  rw [e1, e2, ← intervalIntegral.integral_add i1 i2]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  ring

lemma stl2_m0 (h : ℝ) : ∫ x in (0:ℝ)..h, 2 * (h - x) = h ^ 2 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun x : ℝ => 2 * h * x - x ^ 2) (2 * (h - x)) x := by
    intro x _
    have := ((hasDerivAt_id' x).const_mul (2 * h)).sub (hasDerivAt_pow 2 x)
    refine this.congr_deriv ?_
    norm_num <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => 2 * (h - x)).intervalIntegrable _ _)]
  simp <;> ring

lemma stl2_m2 (h : ℝ) : ∫ x in (0:ℝ)..h, x ^ 2 * (2 * (h - x)) = h ^ 4 / 6 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) h,
      HasDerivAt (fun x : ℝ => 2 * h / 3 * x ^ 3 - x ^ 4 / 2) (x ^ 2 * (2 * (h - x))) x := by
    intro x _
    have := ((hasDerivAt_pow 3 x).const_mul (2 * h / 3)).sub ((hasDerivAt_pow 4 x).div_const 2)
    refine this.congr_deriv ?_
    norm_num <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => x ^ 2 * (2 * (h - x))).intervalIntegrable _ _)]
  simp <;> ring

theorem solution (R r : ℝ) (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / Real.sqrt 2) :
    E R r (fun a b => (a.1 - b.1) ^ 2) = (R ^ 2 - Real.sqrt 2 * R * r + r ^ 2) / 6 := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = R / Real.sqrt 2 := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; exact div_pos hR hs2
  have hh2 : h ^ 2 = R ^ 2 / 2 := by rw [hh, div_pow, hsq]
  have hzone : zone R = {p : ℝ × ℝ | |p.1| + |p.2| ≤ h} := by rw [hh]; rfl
  have hzm : MeasurableSet (zone R) := by
    rw [hzone]; exact measurableSet_le (by fun_prop) measurable_const
  have hinner : ∀ u : ℝ × ℝ, ∫ b in zone R, ((shrink R r • u).1 - b.1) ^ 2 =
      2 * (shrink R r * u.1) ^ 2 * h ^ 2 + h ^ 4 / 3 := by
    intro u
    have e : (shrink R r • u).1 = shrink R r * u.1 := by simp
    rw [e, hzone, stl2_zone_int h hh0.le (fun x => (shrink R r * u.1 - x) ^ 2) (by fun_prop),
      stl2_fold h hh0.le (fun x => (shrink R r * u.1 - x) ^ 2) (by fun_prop)]
    have hf : ∀ x : ℝ, ((shrink R r * u.1 - x) ^ 2 + (shrink R r * u.1 - -x) ^ 2) * (2 * (h - x)) =
        (2 * (shrink R r * u.1) ^ 2) * (2 * (h - x)) + 2 * (x ^ 2 * (2 * (h - x))) := fun x => by ring
    simp_rw [hf]
    have i1 : IntervalIntegrable (fun x : ℝ => (2 * (shrink R r * u.1) ^ 2) * (2 * (h - x))) volume 0 h :=
      (by fun_prop : Continuous fun x : ℝ => (2 * (shrink R r * u.1) ^ 2) * (2 * (h - x))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x : ℝ => 2 * (x ^ 2 * (2 * (h - x)))) volume 0 h :=
      (by fun_prop : Continuous fun x : ℝ => 2 * (x ^ 2 * (2 * (h - x)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul (2 * (shrink R r * u.1) ^ 2), stl2_m0,
      intervalIntegral.integral_const_mul (2 : ℝ), stl2_m2]
    ring
  have hE : E R r (fun a b => (a.1 - b.1) ^ 2) =
      1 / R ^ 4 * ∫ u in zone R, (2 * (shrink R r * u.1) ^ 2 * h ^ 2 + h ^ 4 / 3) := by
    unfold E
    congr 1
    apply setIntegral_congr_fun hzm
    intro u _
    exact hinner u
  rw [hE, hzone, stl2_zone_int h hh0.le (fun x => 2 * (shrink R r * x) ^ 2 * h ^ 2 + h ^ 4 / 3)
      (by fun_prop),
    stl2_fold h hh0.le (fun x => 2 * (shrink R r * x) ^ 2 * h ^ 2 + h ^ 4 / 3) (by fun_prop)]
  have hf : ∀ x : ℝ, ((2 * (shrink R r * x) ^ 2 * h ^ 2 + h ^ 4 / 3) +
      (2 * (shrink R r * -x) ^ 2 * h ^ 2 + h ^ 4 / 3)) * (2 * (h - x)) =
      (4 * shrink R r ^ 2 * h ^ 2) * (x ^ 2 * (2 * (h - x))) + (2 * h ^ 4 / 3) * (2 * (h - x)) :=
    fun x => by ring
  simp_rw [hf]
  have i1 : IntervalIntegrable (fun x : ℝ => (4 * shrink R r ^ 2 * h ^ 2) * (x ^ 2 * (2 * (h - x)))) volume 0 h :=
    (by fun_prop : Continuous fun x : ℝ => (4 * shrink R r ^ 2 * h ^ 2) * (x ^ 2 * (2 * (h - x)))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => (2 * h ^ 4 / 3) * (2 * (h - x))) volume 0 h :=
    (by fun_prop : Continuous fun x : ℝ => (2 * h ^ 4 / 3) * (2 * (h - x))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul (4 * shrink R r ^ 2 * h ^ 2), stl2_m2,
    intervalIntegral.integral_const_mul (2 * h ^ 4 / 3), stl2_m0]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = r / R := ⟨_, rfl⟩
  have hr' : r = u * R := by rw [hu]; field_simp
  have hs : shrink R r = 1 - Real.sqrt 2 * u := by unfold shrink; rw [hu]; ring
  have hh6 : h ^ 6 = R ^ 6 / 8 := by
    have : h ^ 6 = (h ^ 2) ^ 3 := by ring
    rw [this, hh2]; ring
  have hh4 : h ^ 4 = R ^ 4 / 4 := by
    have : h ^ 4 = (h ^ 2) ^ 2 := by ring
    rw [this, hh2]; ring
  have e1 : (4 * shrink R r ^ 2 * h ^ 2) * (h ^ 4 / 6) + (2 * h ^ 4 / 3) * h ^ 2 =
      (2 / 3) * (shrink R r ^ 2 + 1) * h ^ 6 := by ring
  have hR4 : R ^ 4 ≠ 0 := by positivity
  have hcalc : 1 / R ^ 4 * ((2 / 3) * (shrink R r ^ 2 + 1) * h ^ 6) =
      (R ^ 2 / 12) * (shrink R r ^ 2 + 1) := by
    rw [hh6]; field_simp; ring
  have hsq1 : shrink R r ^ 2 + 1 = 2 - 2 * Real.sqrt 2 * u + 2 * u ^ 2 := by
    rw [hs]; linear_combination u ^ 2 * hsq
  rw [e1, hcalc, hsq1, hr']
  ring
