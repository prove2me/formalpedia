-- Prove2me | solution 1 for TaoFivePrimes.sum_sub_integral_le_half_deriv_L1
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:59:04.989542+00:00
-- url     : https://prove2.me/submissions/130d5f24-ebc4-476e-ba76-4fb1a23324bb

import Mathlib

open MeasureTheory intervalIntegral

namespace TaoL31

variable {F : ℝ → ℂ}

theorem hcs_iteratedDeriv (k : ℕ) : ∀ (F : ℝ → ℂ), HasCompactSupport F →
    HasCompactSupport (iteratedDeriv k F) := by
  induction k with
  | zero => intro F hF; simpa [iteratedDeriv_zero] using hF
  | succ k ih =>
      intro F hF
      rw [show iteratedDeriv (k+1) F = iteratedDeriv k (deriv F) from iteratedDeriv_succ']
      exact ih (deriv F) hF.deriv

theorem cont_deriv (hF : ContDiff ℝ (⊤ : ℕ∞) F) : Continuous (deriv F) := by
  have := ContDiff.continuous_iteratedDeriv 1 hF (by exact_mod_cast le_top)
  simpa [iteratedDeriv_one] using this

theorem integrable_norm_deriv (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    Integrable (fun y => ‖deriv F y‖) :=
  ((cont_deriv hF).norm).integrable_of_hasCompactSupport (hc.deriv.norm)

theorem integrable_norm (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    Integrable (fun y => ‖F y‖) :=
  (hF.continuous.norm).integrable_of_hasCompactSupport hc.norm

/-- The fundamental-theorem step: inside a window, any two values of `‖F‖` differ by at most
the total variation of `F` across the window. -/
theorem norm_le_add_integral (hF : ContDiff ℝ (⊤ : ℕ∞) F) {a b y z : ℝ}
    (hy : y ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b) :
    ‖F z‖ ≤ ‖F y‖ + ∫ t in a..b, ‖deriv F t‖ := by
  have hcd : Continuous (deriv F) := cont_deriv hF
  have hFTC : ∫ t in y..z, deriv F t = F z - F y := by
    refine intervalIntegral.integral_deriv_eq_sub (fun t _ => hF.differentiable (by simp) t) ?_
    exact (hcd.intervalIntegrable _ _)
  have h1 : ‖F z - F y‖ ≤ |∫ t in y..z, ‖deriv F t‖| := by
    rw [← hFTC]
    exact intervalIntegral.norm_integral_le_abs_integral_norm
  have hmono : ∀ {u v : ℝ}, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u ≤ v →
      (∫ t in u..v, ‖deriv F t‖) ≤ ∫ t in a..b, ‖deriv F t‖ := by
    intro u v hu hv huv
    refine intervalIntegral.integral_mono_interval hu.1 huv hv.2 ?_
      ((hcd.norm).intervalIntegrable _ _)
    filter_upwards with t using norm_nonneg _
  have h2 : |∫ t in y..z, ‖deriv F t‖| ≤ ∫ t in a..b, ‖deriv F t‖ := by
    rcases le_total y z with h | h
    · rw [abs_of_nonneg (intervalIntegral.integral_nonneg h (fun t _ => norm_nonneg _))]
      exact hmono hy hz h
    · rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg h (fun t _ => norm_nonneg _))]
      exact hmono hz hy h
  calc ‖F z‖ = ‖F y + (F z - F y)‖ := by ring_nf
    _ ≤ ‖F y‖ + ‖F z - F y‖ := norm_add_le _ _
    _ ≤ ‖F y‖ + ∫ t in a..b, ‖deriv F t‖ := by linarith


/-- The unit window around an integer carries `‖F n‖`. -/
theorem window_bound (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : ℝ) :
    ‖F c‖ ≤ (∫ y in (c-1/2)..(c+1/2), ‖F y‖)
      + (1/2) * ∫ y in (c-1/2)..(c+1/2), ‖deriv F y‖ := by
  have hcd : Continuous (deriv F) := cont_deriv hF
  have hcF : Continuous (fun y => ‖F y‖) := hF.continuous.norm
  set a : ℝ := c - 1/2 with ha
  set b : ℝ := c + 1/2 with hb
  have hac : a ≤ c := by rw [ha]; linarith
  have hcb : c ≤ b := by rw [hb]; linarith
  have hab : a ≤ b := le_trans hac hcb
  set L : ℝ := ∫ t in a..c, ‖deriv F t‖ with hL
  set R : ℝ := ∫ t in c..b, ‖deriv F t‖ with hR
  -- comparison on the two halves
  have hleft : ∀ y ∈ Set.Icc a c, ‖F c‖ ≤ ‖F y‖ + L :=
    fun y hy => norm_le_add_integral hF (a := a) (b := c) hy ⟨hac, le_rfl⟩
  have hright : ∀ y ∈ Set.Icc c b, ‖F c‖ ≤ ‖F y‖ + R :=
    fun y hy => norm_le_add_integral hF (a := c) (b := b) hy ⟨le_rfl, hcb⟩
  have hIL : (∫ _y in a..c, ‖F c‖) ≤ ∫ y in a..c, (‖F y‖ + L) := by
    refine intervalIntegral.integral_mono_on hac intervalIntegrable_const ?_ hleft
    exact ((hcF.intervalIntegrable _ _).add intervalIntegrable_const)
  have hIR : (∫ _y in c..b, ‖F c‖) ≤ ∫ y in c..b, (‖F y‖ + R) := by
    refine intervalIntegral.integral_mono_on hcb intervalIntegrable_const ?_ hright
    exact ((hcF.intervalIntegrable _ _).add intervalIntegrable_const)
  rw [intervalIntegral.integral_add (hcF.intervalIntegrable _ _) intervalIntegrable_const] at hIL
  rw [intervalIntegral.integral_add (hcF.intervalIntegrable _ _) intervalIntegrable_const] at hIR
  rw [intervalIntegral.integral_const] at hIL hIR
  rw [intervalIntegral.integral_const] at hIL hIR
  have hsplitF : (∫ y in a..c, ‖F y‖) + (∫ y in c..b, ‖F y‖) = ∫ y in a..b, ‖F y‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _)
  have hsplitD : L + R = ∫ y in a..b, ‖deriv F y‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hcd.norm).intervalIntegrable _ _) ((hcd.norm).intervalIntegrable _ _)
  have hca : c - a = 1/2 := by rw [ha]; ring
  have hbc : b - c = 1/2 := by rw [hb]; ring
  rw [hca] at hIL
  rw [hbc] at hIR
  simp only [smul_eq_mul] at hIL hIR
  linarith [hIL, hIR, hsplitF, hsplitD]


/-- The unit windows around the integers tile the line. -/
theorem iUnion_window : (⋃ n : ℤ, Set.Ioc ((n:ℝ) - 1/2) ((n:ℝ) + 1/2)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
  refine ⟨⌈x - 1/2⌉, ?_, ?_⟩
  · have := Int.ceil_lt_add_one (x - 1/2)
    have h : ((⌈x - 1/2⌉ : ℤ) : ℝ) < x + 1/2 := by linarith
    linarith
  · have := Int.le_ceil (x - 1/2)
    linarith

theorem window_disjoint : Pairwise (Function.onFun Disjoint
    (fun n : ℤ => Set.Ioc ((n:ℝ) - 1/2) ((n:ℝ) + 1/2))) := by
  intro m n hmn
  simp only [Function.onFun, Set.disjoint_left, Set.mem_Ioc]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  have hd : (1:ℝ) ≤ |((m : ℝ)) - (n : ℝ)| := by
    have h0 : m - n ≠ 0 := sub_ne_zero_of_ne hmn
    have h1 : (1:ℤ) ≤ |m - n| := by
      rcases lt_or_gt_of_ne h0 with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    have h' : ((|m - n| : ℤ) : ℝ) = |((m:ℝ)) - (n:ℝ)| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    calc (1:ℝ) = ((1:ℤ) : ℝ) := by norm_num
      _ ≤ ((|m - n| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |((m:ℝ)) - (n:ℝ)| := h'
  rcases abs_cases ((m:ℝ) - (n:ℝ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hd <;> linarith

/-- **Tao, Lemma 3.1, equation (3.2).**
`∑_{n ∈ ℤ} |F(n)| ≤ ‖F‖_{L¹(ℝ)} + ½ ‖F'‖_{L¹(ℝ)}`, and hence
`|∑_{n} F(n) e(αn)| ≤ ∑_n |F(n)|` is bounded by the same quantity. -/
theorem lo_f1 (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    ∑' n : ℤ, ‖F (n : ℝ)‖
      ≤ (∫ y : ℝ, ‖F y‖) + (1/2) * ∫ y : ℝ, ‖deriv F y‖ := by
  set s : ℤ → Set ℝ := fun n => Set.Ioc ((n:ℝ) - 1/2) ((n:ℝ) + 1/2) with hs
  have hm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioc
  have hIF : Integrable (fun y => ‖F y‖) := integrable_norm hF hc
  have hID : Integrable (fun y => ‖deriv F y‖) := integrable_norm_deriv hF hc
  have hsumF : HasSum (fun n : ℤ => ∫ y in s n, ‖F y‖) (∫ y : ℝ, ‖F y‖) := by
    have h := MeasureTheory.hasSum_integral_iUnion hm window_disjoint
      (by rw [hs, iUnion_window]; exact hIF.integrableOn)
    rwa [hs, iUnion_window, MeasureTheory.setIntegral_univ] at h
  have hsumD : HasSum (fun n : ℤ => ∫ y in s n, ‖deriv F y‖) (∫ y : ℝ, ‖deriv F y‖) := by
    have h := MeasureTheory.hasSum_integral_iUnion hm window_disjoint
      (by rw [hs, iUnion_window]; exact hID.integrableOn)
    rwa [hs, iUnion_window, MeasureTheory.setIntegral_univ] at h
  have hsumR : HasSum (fun n : ℤ => (∫ y in s n, ‖F y‖) + (1/2) * ∫ y in s n, ‖deriv F y‖)
      ((∫ y : ℝ, ‖F y‖) + (1/2) * ∫ y : ℝ, ‖deriv F y‖) :=
    hsumF.add (hsumD.mul_left (1/2))
  have hle : ∀ n : ℤ, ‖F (n : ℝ)‖
      ≤ (∫ y in s n, ‖F y‖) + (1/2) * ∫ y in s n, ‖deriv F y‖ := by
    intro n
    have hI1 : (∫ y in s n, ‖F y‖) = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), ‖F y‖ :=
      (intervalIntegral.integral_of_le (by linarith)).symm
    have hI2 : (∫ y in s n, ‖deriv F y‖)
        = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), ‖deriv F y‖ :=
      (intervalIntegral.integral_of_le (by linarith)).symm
    rw [hI1, hI2]
    exact window_bound hF (n : ℝ)
  have hLsummable : Summable (fun n : ℤ => ‖F (n : ℝ)‖) :=
    hsumR.summable.of_nonneg_of_le (fun n => norm_nonneg _) hle
  calc ∑' n : ℤ, ‖F (n : ℝ)‖
      ≤ ∑' n : ℤ, ((∫ y in s n, ‖F y‖) + (1/2) * ∫ y in s n, ‖deriv F y‖) :=
        hLsummable.tsum_le_tsum hle hsumR.summable
    _ = (∫ y : ℝ, ‖F y‖) + (1/2) * ∫ y : ℝ, ‖deriv F y‖ := hsumR.tsum_eq


theorem norm_sub_le_integral (hF : ContDiff ℝ (⊤ : ℕ∞) F) {a b y z : ℝ}
    (hy : y ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b) :
    ‖F z - F y‖ ≤ ∫ t in a..b, ‖deriv F t‖ := by
  have hcd : Continuous (deriv F) := cont_deriv hF
  have hFTC : ∫ t in y..z, deriv F t = F z - F y := by
    refine intervalIntegral.integral_deriv_eq_sub (fun t _ => hF.differentiable (by simp) t) ?_
    exact (hcd.intervalIntegrable _ _)
  have h1 : ‖F z - F y‖ ≤ |∫ t in y..z, ‖deriv F t‖| := by
    rw [← hFTC]
    exact intervalIntegral.norm_integral_le_abs_integral_norm
  have hmono : ∀ {u v : ℝ}, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u ≤ v →
      (∫ t in u..v, ‖deriv F t‖) ≤ ∫ t in a..b, ‖deriv F t‖ := by
    intro u v hu hv huv
    refine intervalIntegral.integral_mono_interval hu.1 huv hv.2 ?_
      ((hcd.norm).intervalIntegrable _ _)
    filter_upwards with t using norm_nonneg _
  have h2 : |∫ t in y..z, ‖deriv F t‖| ≤ ∫ t in a..b, ‖deriv F t‖ := by
    rcases le_total y z with h | h
    · rw [abs_of_nonneg (intervalIntegral.integral_nonneg h (fun t _ => norm_nonneg _))]
      exact hmono hy hz h
    · rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg h (fun t _ => norm_nonneg _))]
      exact hmono hz hy h
  linarith

/-- The trapezoidal-rule step on a single unit window. -/
theorem window_trapezoid (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : ℝ) :
    ‖F c - ∫ y in (c-1/2)..(c+1/2), F y‖
      ≤ (1/2) * ∫ y in (c-1/2)..(c+1/2), ‖deriv F y‖ := by
  have hcd : Continuous (deriv F) := cont_deriv hF
  have hcF : Continuous F := hF.continuous
  set a : ℝ := c - 1/2 with ha
  set b : ℝ := c + 1/2 with hb
  have hac : a ≤ c := by rw [ha]; linarith
  have hcb : c ≤ b := by rw [hb]; linarith
  have hab : a ≤ b := le_trans hac hcb
  set L : ℝ := ∫ t in a..c, ‖deriv F t‖ with hL
  set R : ℝ := ∫ t in c..b, ‖deriv F t‖ with hR
  have hconst : (∫ _y in a..b, F c) = F c := by
    rw [intervalIntegral.integral_const, ha, hb]
    norm_num
  have hrepr : F c - (∫ y in a..b, F y) = ∫ y in a..b, (F c - F y) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcF.intervalIntegrable _ _),
      hconst]
  rw [hrepr]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
  have hcont : Continuous (fun y => ‖F c - F y‖) := (continuous_const.sub hcF).norm
  have hsplitN : (∫ y in a..c, ‖F c - F y‖) + (∫ y in c..b, ‖F c - F y‖)
      = ∫ y in a..b, ‖F c - F y‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hIL : (∫ y in a..c, ‖F c - F y‖) ≤ ∫ _y in a..c, L := by
    refine intervalIntegral.integral_mono_on hac (hcont.intervalIntegrable _ _)
      intervalIntegrable_const (fun y hy => ?_)
    exact norm_sub_le_integral hF (a := a) (b := c) hy ⟨hac, le_rfl⟩
  have hIR : (∫ y in c..b, ‖F c - F y‖) ≤ ∫ _y in c..b, R := by
    refine intervalIntegral.integral_mono_on hcb (hcont.intervalIntegrable _ _)
      intervalIntegrable_const (fun y hy => ?_)
    exact norm_sub_le_integral hF (a := c) (b := b) hy ⟨le_rfl, hcb⟩
  rw [intervalIntegral.integral_const] at hIL hIR
  have hca : c - a = 1/2 := by rw [ha]; ring
  have hbc : b - c = 1/2 := by rw [hb]; ring
  rw [hca] at hIL
  rw [hbc] at hIR
  simp only [smul_eq_mul] at hIL hIR
  have hsplitD : L + R = ∫ y in a..b, ‖deriv F y‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hcd.norm).intervalIntegrable _ _) ((hcd.norm).intervalIntegrable _ _)
  linarith [hIL, hIR, hsplitN, hsplitD]

/-- **Tao, Lemma 3.1, equation (3.1) (the trapezoidal rule).**
`∑_{n ∈ ℤ} F(n) = ∫_ℝ F + O*(½‖F'‖_{L¹})`. -/
theorem lo_f0 (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    ‖(∑' n : ℤ, F (n : ℝ)) - ∫ y : ℝ, F y‖ ≤ (1/2) * ∫ y : ℝ, ‖deriv F y‖ := by
  set s : ℤ → Set ℝ := fun n => Set.Ioc ((n:ℝ) - 1/2) ((n:ℝ) + 1/2) with hs
  have hm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioc
  have hIF : Integrable F := hF.continuous.integrable_of_hasCompactSupport hc
  have hID : Integrable (fun y => ‖deriv F y‖) := integrable_norm_deriv hF hc
  have hsumF : HasSum (fun n : ℤ => ∫ y in s n, F y) (∫ y : ℝ, F y) := by
    have h := MeasureTheory.hasSum_integral_iUnion hm window_disjoint
      (by rw [hs, iUnion_window]; exact hIF.integrableOn)
    rwa [hs, iUnion_window, MeasureTheory.setIntegral_univ] at h
  have hsumD : HasSum (fun n : ℤ => ∫ y in s n, ‖deriv F y‖) (∫ y : ℝ, ‖deriv F y‖) := by
    have h := MeasureTheory.hasSum_integral_iUnion hm window_disjoint
      (by rw [hs, iUnion_window]; exact hID.integrableOn)
    rwa [hs, iUnion_window, MeasureTheory.setIntegral_univ] at h
  have hle : ∀ n : ℤ, ‖F (n:ℝ) - ∫ y in s n, F y‖
      ≤ (1/2) * ∫ y in s n, ‖deriv F y‖ := by
    intro n
    have h1 : (∫ y in s n, F y) = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), F y :=
      (intervalIntegral.integral_of_le (by linarith)).symm
    have h2 : (∫ y in s n, ‖deriv F y‖)
        = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), ‖deriv F y‖ :=
      (intervalIntegral.integral_of_le (by linarith)).symm
    rw [h1, h2]
    exact window_trapezoid hF (n : ℝ)
  -- the difference family is summable and its sum is the difference of the sums
  have hLsummable : Summable (fun n : ℤ => ‖F (n:ℝ)‖) := by
    have hb : ∀ n : ℤ, ‖F (n:ℝ)‖
        ≤ (∫ y in s n, ‖F y‖) + (1/2) * ∫ y in s n, ‖deriv F y‖ := by
      intro n
      have h1 : (∫ y in s n, ‖F y‖) = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), ‖F y‖ :=
        (intervalIntegral.integral_of_le (by linarith)).symm
      have h2 : (∫ y in s n, ‖deriv F y‖)
          = ∫ y in ((n:ℝ) - 1/2)..((n:ℝ) + 1/2), ‖deriv F y‖ :=
        (intervalIntegral.integral_of_le (by linarith)).symm
      rw [h1, h2]
      exact window_bound hF (n : ℝ)
    have hIN : Integrable (fun y => ‖F y‖) := integrable_norm hF hc
    have hsumN : HasSum (fun n : ℤ => ∫ y in s n, ‖F y‖) (∫ y : ℝ, ‖F y‖) := by
      have h := MeasureTheory.hasSum_integral_iUnion hm window_disjoint
        (by rw [hs, iUnion_window]; exact hIN.integrableOn)
      rwa [hs, iUnion_window, MeasureTheory.setIntegral_univ] at h
    exact (hsumN.add (hsumD.mul_left (1/2))).summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hb
  have hsumFval : Summable (fun n : ℤ => F (n:ℝ)) := hLsummable.of_norm
  have hdiff : HasSum (fun n : ℤ => F (n:ℝ) - ∫ y in s n, F y)
      ((∑' n : ℤ, F (n:ℝ)) - ∫ y : ℝ, F y) :=
    hsumFval.hasSum.sub hsumF
  have hRsum : HasSum (fun n : ℤ => (1/2) * ∫ y in s n, ‖deriv F y‖)
      ((1/2) * ∫ y : ℝ, ‖deriv F y‖) := hsumD.mul_left (1/2)
  have hnormsummable : Summable (fun n : ℤ => ‖F (n:ℝ) - ∫ y in s n, F y‖) :=
    hRsum.summable.of_nonneg_of_le (fun n => norm_nonneg _) hle
  calc ‖(∑' n : ℤ, F (n:ℝ)) - ∫ y : ℝ, F y‖
      = ‖∑' n : ℤ, (F (n:ℝ) - ∫ y in s n, F y)‖ := by rw [hdiff.tsum_eq]
    _ ≤ ∑' n : ℤ, ‖F (n:ℝ) - ∫ y in s n, F y‖ :=
        norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℤ, (1/2) * ∫ y in s n, ‖deriv F y‖ :=
        hnormsummable.tsum_le_tsum hle hRsum.summable
    _ = (1/2) * ∫ y : ℝ, ‖deriv F y‖ := hRsum.tsum_eq

end TaoL31

theorem solution (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    ‖(∑' n : ℤ, F (n : ℝ)) - ∫ y : ℝ, F y‖ ≤ (1/2) * ∫ y : ℝ, ‖deriv F y‖ :=
  TaoL31.lo_f0 hF hc
