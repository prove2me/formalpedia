-- Prove2me | solution 1 for ScarceTesting.PerfectTest.delta_gamma_pos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:59:26.97122+00:00
-- url     : https://prove2.me/submissions/36b6cdba-ad80-4c9d-a3b0-a585cf527f56

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set ScarceTesting.PerfectTest

/-- A weighted integral of a nonnegative function is positive when the weight is positive
in the interior and the unweighted integral is positive. -/
lemma wpos (f w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hw : Continuous w) (hf0 : ∀ x ∈ Ioo a b, 0 ≤ f x) (hw0 : ∀ x ∈ Ioo a b, 0 < w x)
    (hint : 0 < ∫ x in a..b, f x) : 0 < ∫ x in a..b, w x * f x := by
  have hfi : IntegrableOn f (Ioo a b) volume := by
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hf
    exact this
  have hwfi : IntegrableOn (fun x => w x * f x) (Ioo a b) volume := by
    have h1 : IntegrableOn f (Icc a b) volume := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf
      exact hf
    have : IntegrableOn (fun x => w x * f x) (Icc a b) volume :=
      h1.continuousOn_mul hw.continuousOn isCompact_Icc
    exact this.mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hint ⊢
  have hnn : 0 ≤ ∫ x in Ioo a b, w x * f x :=
    setIntegral_nonneg measurableSet_Ioo (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))
  rcases hnn.lt_or_eq with h | h
  · exact h
  exfalso
  have hae : (fun x => w x * f x) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
        (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))) ) hwfi).1 h.symm
    exact this
  have hf_ae : f =ᵐ[volume.restrict (Ioo a b)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    have := (hw0 x hxm).ne'
    simpa [this] using hx
  have : ∫ x in Ioo a b, f x = 0 := integral_eq_zero_of_ae hf_ae
  linarith

theorem solution (f : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hf : IsPriorDensity f) (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c := by
  have hi := hf.integrable
  have hi0c : IntervalIntegrable f volume 0 c :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc0.le]; exact Icc_subset_Icc le_rfl hc1.le)
  have hic1 : IntervalIntegrable f volume c 1 :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc1.le]; exact Icc_subset_Icc hc0.le le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi0c hic1
  rw [hf.total] at hsum
  have hnn : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ f x := fun x hx => hf.nonneg x (Ioo_subset_Icc_self hx)
  constructor
  · apply wpos f (fun x => 1 - x) c 1 hc1.le hic1 (by fun_prop)
    · intro x hx; exact hnn x ⟨hc0.trans hx.1, hx.2⟩
    · intro x hx; linarith [hx.2]
    · have : cdf f c = ∫ t in (0:ℝ)..c, f t := rfl
      linarith
  · apply wpos f (fun x => x) 0 c hc0.le hi0c (by fun_prop)
    · intro x hx; exact hnn x ⟨hx.1, hx.2.trans hc1⟩
    · intro x hx; exact hx.1
    · exact hFc0
