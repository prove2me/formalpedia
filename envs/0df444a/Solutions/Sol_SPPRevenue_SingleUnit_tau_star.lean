-- Prove2me | solution 1 for SPPRevenue.SingleUnit.tau_star
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:03:28.735895+00:00
-- url     : https://prove2.me/submissions/375630f9-b0da-48d3-8494-0215d5abed00

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

section

open Real

namespace SPPNum

/-- polynomial lower bound for 1 - exp(-u) on [0,1]. -/
noncomputable def Lpoly (u : ℝ) : ℝ :=
  u - u^2/2 + u^3/6 - u^4/24 + u^5/120 - u^6/720 + u^7/5040 - u^8 * (9/322560)

lemma one_sub_exp_ge (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Lpoly u ≤ 1 - Real.exp (-u) := by
  have hx : |(-u)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hx (n := 8) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  have h' := (abs_le.1 h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  unfold Lpoly
  norm_num at h' ⊢
  nlinarith [h']

/-- antiderivative of Lpoly (1/τ). -/
noncomputable def Fanti (τ : ℝ) : ℝ :=
  Real.log τ + (1/2) * (τ⁻¹)^1 - (1/12) * (τ⁻¹)^2 + (1/72) * (τ⁻¹)^3 - (1/480) * (τ⁻¹)^4
    + (1/3600) * (τ⁻¹)^5 - (1/30240) * (τ⁻¹)^6 + (9/2257920) * (τ⁻¹)^7

lemma hasDerivAt_Fanti (τ : ℝ) (hτ : τ ≠ 0) : HasDerivAt Fanti (Lpoly (1/τ)) τ := by
  have hi := hasDerivAt_inv hτ
  have h := (((((((((Real.hasDerivAt_log hτ).add ((hi.pow 1).const_mul (1/2 : ℝ))).sub
    ((hi.pow 2).const_mul (1/12 : ℝ))).add ((hi.pow 3).const_mul (1/72 : ℝ))).sub
    ((hi.pow 4).const_mul (1/480 : ℝ))).add ((hi.pow 5).const_mul (1/3600 : ℝ))).sub
    ((hi.pow 6).const_mul (1/30240 : ℝ))).add ((hi.pow 7).const_mul (9/2257920 : ℝ))))
  refine h.congr_deriv ?_
  unfold Lpoly
  simp only [one_div, ← inv_pow]
  push_cast
  ring

end SPPNum

namespace SPPNum

lemma exp_negc_bounds :
    (0.5896064 : ℝ) ≤ Real.exp (-(5283/10000)) ∧ Real.exp (-(5283/10000)) ≤ (0.5896065 : ℝ) := by
  have hx : |(-(5283/10000 : ℝ))| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h' := abs_le.1 h
  norm_num at h'
  constructor <;> linarith [h'.1, h'.2]

end SPPNum

namespace SPPNum

lemma integral_lower_bound :
    Real.exp (-1) ≤ ∫ τ in (1:ℝ)..Real.exp (5283/10000), (1 - Real.exp (-(1 / τ))) := by
  set T := Real.exp (5283/10000) with hTdef
  have hT1 : 1 ≤ T := Real.one_le_exp (by norm_num)
  have hne : ∀ x ∈ Set.uIcc 1 T, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hT1] at hx; linarith [hx.1]
  have hintL : IntervalIntegrable (fun τ => Lpoly (1 / τ)) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by unfold Lpoly; fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hintf : IntervalIntegrable (fun τ => 1 - Real.exp (-(1 / τ))) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hmono : ∫ τ in (1:ℝ)..T, Lpoly (1 / τ) ≤ ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ))) := by
    refine intervalIntegral.integral_mono_on hT1 hintL hintf fun x hx => ?_
    have hx1 : 1 ≤ x := hx.1
    exact one_sub_exp_ge (1 / x) (by positivity) (by rw [div_le_one (by linarith)]; exact hx1)
  have hftc : ∫ τ in (1:ℝ)..T, Lpoly (1 / τ) = Fanti T - Fanti 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_Fanti x (hne x hx)) hintL
  refine le_trans ?_ (hftc ▸ hmono)
  have hTinv : T⁻¹ = Real.exp (-(5283/10000)) := by rw [hTdef, Real.exp_neg]
  have hlogT : Real.log T = 5283/10000 := by rw [hTdef, Real.log_exp]
  obtain ⟨hlo, hhi⟩ := exp_negc_bounds
  set y := Real.exp (-(5283/10000 : ℝ))
  have hy0 : (0:ℝ) ≤ 0.5896064 := by norm_num
  unfold Fanti
  rw [hTinv, hlogT, Real.log_one, inv_one]
  have e1 := Real.exp_neg_one_lt_d9
  have l2 := pow_le_pow_left₀ hy0 hlo 2
  have l3 := pow_le_pow_left₀ hy0 hlo 3
  have l4 := pow_le_pow_left₀ hy0 hlo 4
  have l5 := pow_le_pow_left₀ hy0 hlo 5
  have l6 := pow_le_pow_left₀ hy0 hlo 6
  have l7 := pow_le_pow_left₀ hy0 hlo 7
  have hy0' : 0 ≤ y := Real.exp_nonneg _
  have u2 := pow_le_pow_left₀ hy0' hhi 2
  have u4 := pow_le_pow_left₀ hy0' hhi 4
  have u6 := pow_le_pow_left₀ hy0' hhi 6
  norm_num at l2 l3 l4 l5 l6 l7 u2 u4 u6 e1 ⊢
  linarith

end SPPNum

end

section

open Real

namespace SPPNum

noncomputable def Upoly (u : ℝ) : ℝ :=
  u - u^2/2 + u^3/6 - u^4/24 + u^5/120 - u^6/720 + u^7/5040 + u^8 * (9/322560)

lemma one_sub_exp_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    1 - Real.exp (-u) ≤ Upoly u := by
  have hx : |(-u)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hx (n := 8) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  have h' := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  unfold Upoly
  norm_num at h' ⊢
  nlinarith [h']

noncomputable def Fanti2 (τ : ℝ) : ℝ :=
  Real.log τ + (1/2) * (τ⁻¹)^1 - (1/12) * (τ⁻¹)^2 + (1/72) * (τ⁻¹)^3 - (1/480) * (τ⁻¹)^4
    + (1/3600) * (τ⁻¹)^5 - (1/30240) * (τ⁻¹)^6 - (9/2257920) * (τ⁻¹)^7

lemma hasDerivAt_Fanti2 (τ : ℝ) (hτ : τ ≠ 0) : HasDerivAt Fanti2 (Upoly (1/τ)) τ := by
  have hi := hasDerivAt_inv hτ
  have h := (((((((((Real.hasDerivAt_log hτ).add ((hi.pow 1).const_mul (1/2 : ℝ))).sub
    ((hi.pow 2).const_mul (1/12 : ℝ))).add ((hi.pow 3).const_mul (1/72 : ℝ))).sub
    ((hi.pow 4).const_mul (1/480 : ℝ))).add ((hi.pow 5).const_mul (1/3600 : ℝ))).sub
    ((hi.pow 6).const_mul (1/30240 : ℝ))).sub ((hi.pow 7).const_mul (9/2257920 : ℝ))))
  refine h.congr_deriv ?_
  unfold Upoly
  simp only [one_div, ← inv_pow]
  push_cast
  ring

lemma exp_neg528_bounds :
    (0.5897833 : ℝ) ≤ Real.exp (-(528/1000)) ∧ Real.exp (-(528/1000)) ≤ (0.5897834 : ℝ) := by
  have hx : |(-(528/1000 : ℝ))| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h' := abs_le.1 h
  norm_num at h'
  constructor <;> linarith [h'.1, h'.2]

lemma exp528_ge : (16955/10000 : ℝ) ≤ Real.exp (528/1000) := by
  have hx : |((528/1000 : ℝ))| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h' := abs_le.1 h
  norm_num at h'
  linarith [h'.1, h'.2]

lemma exp5283_le : Real.exp (5283/10000) ≤ (16965/10000 : ℝ) := by
  have hx : |((5283/10000 : ℝ))| ≤ 1 := by norm_num [abs_of_nonneg]
  have h := Real.exp_bound hx (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h' := abs_le.1 h
  norm_num at h'
  linarith [h'.1, h'.2]

lemma integral_upper_bound :
    ∫ τ in (1:ℝ)..Real.exp (528/1000), (1 - Real.exp (-(1 / τ))) < Real.exp (-1) := by
  set T := Real.exp (528/1000) with hTdef
  have hT1 : 1 ≤ T := Real.one_le_exp (by norm_num)
  have hne : ∀ x ∈ Set.uIcc 1 T, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hT1] at hx; linarith [hx.1]
  have hintU : IntervalIntegrable (fun τ => Upoly (1 / τ)) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by unfold Upoly; fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hintf : IntervalIntegrable (fun τ => 1 - Real.exp (-(1 / τ))) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hmono : ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ))) ≤ ∫ τ in (1:ℝ)..T, Upoly (1 / τ) := by
    refine intervalIntegral.integral_mono_on hT1 hintf hintU fun x hx => ?_
    have hx1 : 1 ≤ x := hx.1
    exact one_sub_exp_le (1 / x) (by positivity) (by rw [div_le_one (by linarith)]; exact hx1)
  have hftc : ∫ τ in (1:ℝ)..T, Upoly (1 / τ) = Fanti2 T - Fanti2 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_Fanti2 x (hne x hx)) hintU
  refine lt_of_le_of_lt (hftc ▸ hmono) ?_
  have hTinv : T⁻¹ = Real.exp (-(528/1000)) := by rw [hTdef, Real.exp_neg]
  have hlogT : Real.log T = 528/1000 := by rw [hTdef, Real.log_exp]
  obtain ⟨hlo, hhi⟩ := exp_neg528_bounds
  set y := Real.exp (-(528/1000 : ℝ))
  have hy0 : (0:ℝ) ≤ 0.5897833 := by norm_num
  unfold Fanti2
  rw [hTinv, hlogT, Real.log_one, inv_one]
  have e1 := Real.exp_neg_one_gt_d9
  have hy0' : 0 ≤ y := Real.exp_nonneg _
  have l2 := pow_le_pow_left₀ hy0 hlo 2
  have l4 := pow_le_pow_left₀ hy0 hlo 4
  have l6 := pow_le_pow_left₀ hy0 hlo 6
  have u3 := pow_le_pow_left₀ hy0' hhi 3
  have u5 := pow_le_pow_left₀ hy0' hhi 5
  have l7 := pow_le_pow_left₀ hy0 hlo 7
  norm_num at l2 l4 l6 l7 u3 u5 e1 ⊢
  linarith

/-! The function `H T = ∫_1^T (1 - e^{-1/τ}) dτ`. -/

noncomputable def H (T : ℝ) : ℝ := ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ)))

lemma g_intble (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun τ : ℝ => 1 - Real.exp (-(1 / τ))) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  have : x ≠ 0 := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
    · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1]
  exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt

lemma H_strictMono : StrictMonoOn H (Set.Ici 1) := by
  intro a ha b hb hab
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le one_pos ha
  have hb0 : (0:ℝ) < b := lt_trans ha0 hab
  unfold H
  have hsub := intervalIntegral.integral_interval_sub_left (g_intble 1 b one_pos hb0)
    (g_intble 1 a one_pos ha0)
  have hpos : 0 < ∫ τ in a..b, (1 - Real.exp (-(1 / τ))) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (g_intble a b ha0 hb0) (fun x hx => ?_) hab
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have : Real.exp (-(1 / x)) < 1 := Real.exp_lt_one_iff.2 (by simp; positivity)
    linarith
  linarith

lemma H_cont (X : ℝ) (hX : 1 ≤ X) : ContinuousOn H (Set.Icc 1 X) := by
  have hc : ContinuousOn (fun τ : ℝ => 1 - Real.exp (-(1 / τ))) (Set.uIcc 1 X) := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    have : x ≠ 0 := by linarith [hx.1]
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have h := intervalIntegral.continuousOn_primitive_interval (a := (1:ℝ)) (b := X)
    (μ := MeasureTheory.volume) (hc.integrableOn_compact isCompact_uIcc)
  rw [Set.uIcc_of_le hX] at h
  exact h

end SPPNum

end


open MeasureTheory
open scoped ENNReal
open SPPRevenue.SingleUnit

namespace SPPNum

lemma root_iff (T : ℝ) : frRootEq T ↔ H T = Real.exp (-1) := by
  unfold frRootEq H; constructor <;> intro h <;> linarith

lemma root_bounds (T : ℝ) (hT : 1 ≤ T) (h : H T = Real.exp (-1)) :
    Real.exp (528/1000) < T ∧ T ≤ Real.exp (5283/10000) := by
  have h1 := integral_lower_bound
  have h0 := integral_upper_bound
  have hc0 : (1:ℝ) ≤ Real.exp (528/1000) := Real.one_le_exp (by norm_num)
  have hc1 : (1:ℝ) ≤ Real.exp (5283/10000) := Real.one_le_exp (by norm_num)
  constructor
  · by_contra hc
    push Not at hc
    have := H_strictMono.monotoneOn hT hc0 hc
    unfold H at this h
    linarith
  · by_contra hc
    push Not at hc
    have := H_strictMono hc1 hT hc
    unfold H at this h
    linarith

lemma root_exists : ∃ T, 1 < T ∧ H T = Real.exp (-1) := by
  have hc1 : (1:ℝ) ≤ Real.exp (5283/10000) := Real.one_le_exp (by norm_num)
  have hH1 : H 1 = 0 := by unfold H; simp
  have hmem : Real.exp (-1) ∈ Set.Icc (H 1) (H (Real.exp (5283/10000))) :=
    ⟨by rw [hH1]; exact (Real.exp_pos _).le, integral_lower_bound⟩
  obtain ⟨T, hT, hTeq⟩ := intermediate_value_Icc hc1 (H_cont _ hc1) hmem
  refine ⟨T, lt_of_le_of_ne hT.1 ?_, hTeq⟩
  rintro rfl
  rw [hH1] at hTeq
  exact (Real.exp_pos _).ne' hTeq.symm

end SPPNum

theorem solution :
    (∃! T : ℝ, 1 < T ∧ frRootEq T) ∧
      ∀ T : ℝ, 1 < T → frRootEq T → 16955 / 10000 ≤ T ∧ T ≤ 16965 / 10000 := by
  refine ⟨?_, fun T hT hr => ?_⟩
  · obtain ⟨T, hT, hTeq⟩ := SPPNum.root_exists
    refine ⟨T, ⟨hT, (SPPNum.root_iff T).2 hTeq⟩, fun T' ⟨hT', hr'⟩ => ?_⟩
    rw [SPPNum.root_iff] at hr'
    exact SPPNum.H_strictMono.injOn (Set.mem_Ici.2 hT'.le) (Set.mem_Ici.2 hT.le)
      (hr'.trans hTeq.symm)
  · rw [SPPNum.root_iff] at hr
    obtain ⟨h1, h2⟩ := SPPNum.root_bounds T hT.le hr
    exact ⟨le_trans SPPNum.exp528_ge h1.le, le_trans h2 SPPNum.exp5283_le⟩
