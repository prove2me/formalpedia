-- Prove2me | solution 1 for SPPRevenue.SingleUnit.fr_value
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:05:57.014926+00:00
-- url     : https://prove2.me/submissions/4fd60ee4-b860-4206-869e-d4f515f4a809

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

section

open Real MeasureTheory Set
open scoped ENNReal

namespace SPPParam

variable {T : ℝ} [hT : Fact (1 < T)]

noncomputable def cT (T : ℝ) : ℝ := T
noncomputable def aT (T : ℝ) : ℝ := T⁻¹
noncomputable def fE (x : ℝ) : ℝ := 1 - Real.exp (-x)
noncomputable def lam (T : ℝ) : ℝ := aT T / fE (aT T)
noncomputable def phi (T : ℝ) (y : ℝ) : ℝ := y - lam T * fE y
noncomputable def Gfun (T : ℝ) (B σ : ℝ) : ℝ :=
  if σ ≤ B then phi T 1 else if σ ≤ B * cT T then phi T (B / σ) else 0

lemma fE_pos {x : ℝ} (hx : 0 < x) : 0 < fE x := by
  unfold fE; have := Real.exp_lt_one_iff.2 (show -x < 0 by linarith); linarith

lemma aT_pos : 0 < (aT T) := inv_pos.2 (by linarith [hT.out])
lemma aT_lt_one : (aT T) < 1 := inv_lt_one_of_one_lt₀ hT.out
lemma cT_pos : 0 < (cT T) := by unfold cT; linarith [hT.out]
lemma aT_mul_cT : (aT T) * (cT T) = 1 := by
  unfold aT cT; exact inv_mul_cancel₀ (by linarith [hT.out])

lemma lam_nonneg : 0 ≤ (lam T) := div_nonneg (aT_pos (T := T)).le (fE_pos (aT_pos (T := T))).le

lemma phi_aT : (phi T) (aT T) = 0 := by
  unfold phi lam; have := (fE_pos (aT_pos (T := T))).ne'; field_simp; ring

/-- concavity of `fE` with `fE 0 = 0`. -/
lemma conc (s y : ℝ) (hs0 : 0 ≤ s) (hsy : s ≤ y) (hy : 0 < y) : s * fE y ≤ y * fE s := by
  have hθ0 : 0 ≤ s / y := div_nonneg hs0 hy.le
  have hθ1 : s / y ≤ 1 := (div_le_one hy).2 hsy
  have h := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ (-y)) (sub_nonneg.2 hθ1) hθ0
    (by ring : (1 - s / y) + s / y = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : s / y * -y = -s := by field_simp
  rw [e] at h
  unfold fE
  have h2 : y * Real.exp (-s) ≤ y * (1 - s / y + s / y * Real.exp (-y)) :=
    mul_le_mul_of_nonneg_left h hy.le
  have e2 : y * (1 - s / y + s / y * Real.exp (-y)) = y - s + s * Real.exp (-y) := by
    field_simp
  linarith

lemma phi_le (s y : ℝ) (hs0 : 0 ≤ s) (hsy : s ≤ y) (hy : 0 < y) : (phi T) s ≤ (s / y) * (phi T) y := by
  have h := conc s y hs0 hsy hy
  unfold phi
  have hl := (lam_nonneg (T := T))
  have : (lam T) * (s * fE y) ≤ (lam T) * (y * fE s) := mul_le_mul_of_nonneg_left h hl
  have e : s / y * (y - (lam T) * fE y) = s - (lam T) * (s * fE y) / y := by field_simp
  rw [e]
  have : (lam T) * (s * fE y) / y ≤ (lam T) * fE s := by
    rw [div_le_iff₀ hy]; linarith
  linarith

lemma phi_nonneg {y : ℝ} (hy : (aT T) ≤ y) : 0 ≤ (phi T) y := by
  have hy0 : 0 < y := lt_of_lt_of_le (aT_pos (T := T)) hy
  have h := (phi_le (T := T)) (aT T) y (aT_pos (T := T)).le hy hy0
  rw [(phi_aT (T := T))] at h
  have : 0 < (aT T) / y := div_pos (aT_pos (T := T)) hy0
  by_contra hc; push Not at hc
  nlinarith

lemma pointwise (B σ s : ℝ) (hB : 0 < B) (hσ : 0 < σ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsB : σ * s ≤ B) : s ≤ (lam T) * fE s + (Gfun T) B σ := by
  have key : s - (lam T) * fE s ≤ (Gfun T) B σ := by
    change (phi T) s ≤ _
    unfold Gfun
    split_ifs with h1 h2
    · have h := (phi_le (T := T)) s 1 hs0 hs1 one_pos
      have := (phi_nonneg (T := T)) (aT_lt_one (T := T)).le
      rw [div_one] at h
      nlinarith
    · have hy0 : 0 < B / σ := div_pos hB hσ
      have hsy : s ≤ B / σ := by rw [le_div_iff₀ hσ]; linarith
      have hya : (aT T) ≤ B / σ := by
        rw [le_div_iff₀ hσ]
        have := (aT_mul_cT (T := T))
        nlinarith [(aT_pos (T := T))]
      have h := (phi_le (T := T)) s (B / σ) hs0 hsy hy0
      have hn := (phi_nonneg (T := T)) hya
      have : s / (B / σ) ≤ 1 := (div_le_one hy0).2 hsy
      nlinarith [div_nonneg hs0 hy0.le]
    · have hsa : s ≤ (aT T) := by
        push Not at h2
        have : σ * s ≤ σ * (aT T) := by
          have := (aT_mul_cT (T := T))
          nlinarith [(aT_pos (T := T))]
        exact le_of_mul_le_mul_left this hσ
      have h := (phi_le (T := T)) s (aT T) hs0 hsa (aT_pos (T := T))
      rw [(phi_aT (T := T)), mul_zero] at h
      exact h
  linarith

lemma Gfun_measurable (B : ℝ) : Measurable ((Gfun T) B) := by
  unfold Gfun
  refine Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic ?_ measurable_const)
  unfold phi fE
  fun_prop

end SPPParam

namespace SPPParam

variable {T : ℝ} [hT : Fact (1 < T)]


lemma cT_ge_one : 1 ≤ (cT T) := by unfold cT; exact hT.out.le

lemma int_phi_inv :
    ∫ τ in (1:ℝ)..(cT T), (phi T) (1 / τ) =
      Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T), (1 - Real.exp (-(1 / τ))) := by
  have hne : ∀ x ∈ Set.uIcc 1 (cT T), x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le (cT_ge_one (T := T))] at hx; linarith [hx.1]
  have h0 : (0:ℝ) ∉ Set.uIcc 1 (cT T) := fun h => hne 0 h rfl
  have hint1 : IntervalIntegrable (fun τ : ℝ => 1 / τ) volume 1 (cT T) := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hintf : IntervalIntegrable (fun τ => 1 - Real.exp (-(1 / τ))) volume 1 (cT T) := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have := hne x hx
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  unfold phi fE
  rw [intervalIntegral.integral_sub hint1 (hintf.const_mul (lam T)), intervalIntegral.integral_const_mul,
    integral_one_div h0, div_one]
  rfl

lemma J_eq (B : ℝ) (hB : 0 < B) :
    ∫ σ in B..B * (cT T), (phi T) (B / σ) =
      B * (Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T), (1 - Real.exp (-(1 / τ)))) := by
  have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := (cT T))
    (fun σ => (phi T) (B / σ)) hB.ne'
  rw [mul_one] at h
  rw [← (int_phi_inv (T := T))]
  have hc : ∫ x in (1:ℝ)..(cT T), (phi T) (B / (B * x)) = ∫ x in (1:ℝ)..(cT T), (phi T) (1 / x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (cT_ge_one (T := T))] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    change (phi T) (B / (B * x)) = (phi T) (1 / x)
    congr 1
    field_simp
  rw [hc] at h
  rw [h, smul_eq_mul]
  field_simp

end SPPParam

namespace SPPParam

variable {T : ℝ} [hT : Fact (1 < T)]


lemma fE_pos' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) := by
  have := Real.exp_le_one_iff.2 (show -x ≤ 0 by linarith); linarith

lemma phi_div_nonneg (B σ : ℝ) (hB : 0 < B) (hσ0 : 0 < σ) (hσ : σ ≤ B * (cT T)) :
    0 ≤ (phi T) (B / σ) := by
  apply (phi_nonneg (T := T))
  rw [le_div_iff₀ hσ0]
  have := (aT_mul_cT (T := T))
  nlinarith [(aT_pos (T := T))]

lemma Gfun_nonneg (B σ : ℝ) (hB : 0 < B) : 0 ≤ (Gfun T) B σ := by
  unfold Gfun
  split_ifs with h1 h2
  · exact (phi_nonneg (T := T)) (aT_lt_one (T := T)).le
  · exact (phi_div_nonneg (T := T)) B σ hB (lt_trans hB (lt_of_not_ge h1)) h2
  · exact le_refl _

lemma J_nonneg (B : ℝ) (hB : 0 < B) :
    0 ≤ B * (Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T), (1 - Real.exp (-(1 / τ)))) := by
  rw [← (J_eq (T := T)) B hB, intervalIntegral.integral_of_le (le_mul_of_one_le_right hB.le (cT_ge_one (T := T)))]
  exact setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
    (phi_div_nonneg (T := T)) B σ hB (lt_trans hB hσ.1) hσ.2

lemma lint_G (B : ℝ) (hB : 0 < B) :
    ∫⁻ σ in Ioi 0, ENNReal.ofReal ((Gfun T) B σ) ≤
      ENNReal.ofReal (B * (phi T) 1 + B * (Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T),
        (1 - Real.exp (-(1 / τ))))) := by
  have hBT : B ≤ B * (cT T) := le_mul_of_one_le_right hB.le (cT_ge_one (T := T))
  have hsub : Ioi (0:ℝ) ⊆ (Ioc 0 B ∪ Ioc B (B * (cT T))) ∪ Ioi (B * (cT T)) := by
    intro x hx
    simp only [mem_union, mem_Ioc, mem_Ioi] at hx ⊢
    by_cases h1 : x ≤ B
    · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · by_cases h2 : x ≤ B * (cT T)
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h1, h2⟩)
      · exact Or.inr (lt_of_not_ge h2)
  have hp1 : 0 ≤ (phi T) 1 := (phi_nonneg (T := T)) (aT_lt_one (T := T)).le
  -- piece 1
  have e1 : ∫⁻ σ in Ioc 0 B, ENNReal.ofReal ((Gfun T) B σ) = ENNReal.ofReal (B * (phi T) 1) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal ((phi T) 1))]
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ← ENNReal.ofReal_mul hp1, mul_comm]
    · intro x hx; simp only [Gfun, if_pos hx.2]
  -- piece 2
  have hcont : ContinuousOn (fun σ => (phi T) (B / σ)) (Icc B (B * (cT T))) := by
    intro x hx
    have : x ≠ 0 := by linarith [hx.1]
    exact (by unfold phi fE; fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have hnn : ∀ σ ∈ Ioc B (B * (cT T)), 0 ≤ (phi T) (B / σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_trans hB hσ.1
    apply (phi_nonneg (T := T))
    rw [le_div_iff₀ hσ0]
    have := (aT_mul_cT (T := T))
    have := hσ.2
    nlinarith [(aT_pos (T := T))]
  have e2 : ∫⁻ σ in Ioc B (B * (cT T)), ENNReal.ofReal ((Gfun T) B σ) =
      ENNReal.ofReal (∫ σ in B..B * (cT T), (phi T) (B / σ)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun σ => ENNReal.ofReal ((phi T) (B / σ)))]
    · rw [intervalIntegral.integral_of_le hBT, ofReal_integral_eq_lintegral_ofReal]
      · exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      · exact ae_restrict_of_forall_mem measurableSet_Ioc hnn
    · intro x hx; simp only [Gfun, if_neg (not_le.2 hx.1), if_pos hx.2]
  have e3 : ∫⁻ σ in Ioi (B * (cT T)), ENNReal.ofReal ((Gfun T) B σ) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)]
    · simp
    · intro x hx
      have hx' : B * (cT T) < x := hx
      simp only [Gfun, if_neg (not_le.2 (lt_of_le_of_lt hBT hx')), if_neg (not_le.2 hx'),
        ENNReal.ofReal_zero]
  calc ∫⁻ σ in Ioi 0, ENNReal.ofReal ((Gfun T) B σ)
      ≤ ∫⁻ σ in (Ioc 0 B ∪ Ioc B (B * (cT T))) ∪ Ioi (B * (cT T)), ENNReal.ofReal ((Gfun T) B σ) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ σ in Ioc 0 B, ENNReal.ofReal ((Gfun T) B σ)) +
          (∫⁻ σ in Ioc B (B * (cT T)), ENNReal.ofReal ((Gfun T) B σ)) +
          ∫⁻ σ in Ioi (B * (cT T)), ENNReal.ofReal ((Gfun T) B σ) := by
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        exact lintegral_union_le _ _ _
    _ = ENNReal.ofReal (B * (phi T) 1) + ENNReal.ofReal (∫ σ in B..B * (cT T), (phi T) (B / σ)) := by
        rw [e1, e2, e3, add_zero]
    _ = _ := by
        rw [← (J_eq (T := T)) B hB, ← ENNReal.ofReal_add (mul_nonneg hB.le hp1)]
        rw [(J_eq (T := T)) B hB]
        exact (J_nonneg (T := T)) B hB

/-- The factor-revealing bound, in unnormalized form. -/
theorem fr_bound (S : ℝ → ℝ≥0∞) (B : ℝ) (hB : 0 < B) (h1 : ∀ σ, S σ ≤ 1)
    (h2 : ∀ σ, 0 < σ → ENNReal.ofReal σ * S σ ≤ ENNReal.ofReal B)
    (h3 : ∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) ≤ ENNReal.ofReal B)
    (hI : Real.exp (-1) ≤ ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ)))) :
    ∫⁻ σ in Ioi 0, S σ ≤ ENNReal.ofReal (B * (1 + Real.log T)) := by
  have hpt : ∀ σ ∈ Ioi (0:ℝ), S σ ≤ ENNReal.ofReal (lam T) *
      ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) + ENNReal.ofReal ((Gfun T) B σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := hσ
    have hfin : S σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h1 σ)
    set s := (S σ).toReal with hs
    have hS : S σ = ENNReal.ofReal s := (ENNReal.ofReal_toReal hfin).symm
    have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
    have hs1 : s ≤ 1 := by
      have := h1 σ; rw [hS] at this; exact (ENNReal.ofReal_le_one).1 this
    have hsB : σ * s ≤ B := by
      have := h2 σ hσ0
      rw [hS, ← ENNReal.ofReal_mul hσ0.le, ENNReal.ofReal_le_ofReal_iff hB.le] at this
      exact this
    have hp := (pointwise (T := T)) B σ s hB hσ0 hs0 hs1 hsB
    rw [hS, ← ENNReal.ofReal_mul (lam_nonneg (T := T))]
    have hf0 : 0 ≤ (lam T) * (1 - Real.exp (-s)) :=
      mul_nonneg (lam_nonneg (T := T)) (fE_pos' hs0)
    rw [← ENNReal.ofReal_add hf0 ((Gfun_nonneg (T := T)) B σ hB)]
    exact ENNReal.ofReal_le_ofReal hp
  calc ∫⁻ σ in Ioi 0, S σ
      ≤ ∫⁻ σ in Ioi 0, (ENNReal.ofReal (lam T) *
          ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) + ENNReal.ofReal ((Gfun T) B σ)) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = ENNReal.ofReal (lam T) * (∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(S σ).toReal))) +
          ∫⁻ σ in Ioi 0, ENNReal.ofReal ((Gfun T) B σ) := by
        rw [lintegral_add_right _ (((Gfun_measurable (T := T)) B).ennreal_ofReal),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (lam T) * ENNReal.ofReal B +
          ENNReal.ofReal (B * (phi T) 1 + B * (Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T),
            (1 - Real.exp (-(1 / τ))))) := by
        gcongr
        exact (lint_G (T := T)) B hB
    _ = ENNReal.ofReal ((lam T) * B + (B * (phi T) 1 + B * (Real.log T - (lam T) * ∫ τ in (1:ℝ)..(cT T),
            (1 - Real.exp (-(1 / τ)))))) := by
        rw [← ENNReal.ofReal_mul (lam_nonneg (T := T)), ENNReal.ofReal_add (mul_nonneg (lam_nonneg (T := T)) hB.le)]
        exact add_nonneg (mul_nonneg hB.le ((phi_nonneg (T := T)) (aT_lt_one (T := T)).le)) ((J_nonneg (T := T)) B hB)
    _ ≤ ENNReal.ofReal (B * (1 + Real.log T)) := by
        apply ENNReal.ofReal_le_ofReal
        have hl := (lam_nonneg (T := T))
        unfold phi fE
        change Real.exp (-1) ≤ ∫ τ in (1:ℝ)..(cT T), (1 - Real.exp (-(1 / τ))) at hI
        nlinarith [mul_nonneg hl hB.le]

end SPPParam

end


open MeasureTheory Set
open scoped ENNReal
open SPPRevenue.SingleUnit

namespace SPPFRV

noncomputable def sOpt (T : ℝ) (τ : ℝ) : ℝ := if τ ≤ 1 then 1 else if τ ≤ T then 1 / τ else 0

lemma root_le (T : ℝ) (hT : 1 < T) (hroot : frRootEq T) : T ≤ Real.exp (5283/10000) := by
  have h : SPPNum.H T = Real.exp (-1) := by unfold frRootEq at hroot; unfold SPPNum.H; linarith
  have h1 := SPPNum.integral_lower_bound
  have hc1 : (1:ℝ) ≤ Real.exp (5283/10000) := Real.one_le_exp (by norm_num)
  by_contra hc
  push Not at hc
  have := SPPNum.H_strictMono hc1 (Set.mem_Ici.2 hT.le) hc
  unfold SPPNum.H at this h
  linarith

lemma upper (T : ℝ) (hT : 1 < T) (hroot : frRootEq T) (s : ℝ → ℝ) (hs : FRFeasible s) :
    frObj s ≤ ENNReal.ofReal (1 + Real.log T) := by
  have : Fact (1 < T) := ⟨hT⟩
  obtain ⟨_, hbd, hint⟩ := hs
  set S : ℝ → ℝ≥0∞ := fun σ => if 0 ≤ σ then ENNReal.ofReal (s σ) else 0 with hSdef
  have hI : Real.exp (-1) ≤ ∫ τ in (1:ℝ)..T, (1 - Real.exp (-(1 / τ))) := by
    unfold frRootEq at hroot; linarith
  have h1 : ∀ σ, S σ ≤ 1 := by
    intro σ; simp only [hSdef]; split_ifs with h
    · exact ENNReal.ofReal_le_one.2 (hbd σ h).2.1
    · exact zero_le
  have h2 : ∀ σ, 0 < σ → ENNReal.ofReal σ * S σ ≤ ENNReal.ofReal 1 := by
    intro σ hσ
    simp only [hSdef, if_pos hσ.le]
    rw [← ENNReal.ofReal_mul hσ.le]
    exact ENNReal.ofReal_le_ofReal (hbd σ hσ.le).2.2
  have hS_Ioi : ∀ σ ∈ Ioi (0:ℝ), S σ = ENNReal.ofReal (s σ) := fun σ hσ => by
    have hσ' : (0:ℝ) < σ := hσ
    simp only [hSdef, if_pos hσ'.le]
  have h3 : ∫⁻ σ in Ioi 0, ENNReal.ofReal (1 - Real.exp (-(S σ).toReal)) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]
    refine le_trans ?_ hint
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun σ => ENNReal.ofReal (1 - Real.exp (-s σ)))
      (fun σ hσ => by rw [hS_Ioi σ hσ, ENNReal.toReal_ofReal (hbd σ (le_of_lt (show (0:ℝ) < σ from hσ))).1])]
    exact lintegral_mono_set Ioi_subset_Ici_self
  have hfr := SPPParam.fr_bound (T := T) S 1 one_pos h1 h2 h3 hI
  rw [one_mul, setLIntegral_congr_fun measurableSet_Ioi hS_Ioi] at hfr
  unfold frObj
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  exact hfr

lemma sOpt_feasible (T : ℝ) (hT : 1 < T) (hroot : frRootEq T) : FRFeasible (sOpt T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha0 : (0:ℝ) ≤ a := ha
    simp only [sOpt]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first
      | exact le_rfl | linarith
      | (rw [div_le_one (by linarith)]; linarith)
      | positivity
      | (exact one_div_le_one_div_of_le (by linarith) hab)
  · intro τ hτ
    simp only [sOpt]
    split_ifs with h1 h2
    · norm_num; exact h1
    · refine ⟨by positivity, ?_, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      · rw [mul_one_div, div_self (by linarith)]
    · norm_num
  · have hsub : Ici (0:ℝ) ⊆ (Icc 0 1 ∪ Ioc 1 T) ∪ Ioi T := by
      intro x hx
      simp only [mem_union, mem_Icc, mem_Ioc, mem_Ioi, mem_Ici] at hx ⊢
      by_cases h1 : x ≤ 1
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · by_cases h2 : x ≤ T
        · exact Or.inl (Or.inr ⟨lt_of_not_ge h1, h2⟩)
        · exact Or.inr (lt_of_not_ge h2)
    have e1 : ∫⁻ σ in Icc 0 1, ENNReal.ofReal (1 - Real.exp (-sOpt T σ)) =
        ENNReal.ofReal (1 - Real.exp (-1)) := by
      rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => ENNReal.ofReal (1 - Real.exp (-1)))]
      · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
      · intro x hx; simp only [sOpt, if_pos hx.2]
    have hcont : ContinuousOn (fun σ : ℝ => 1 - Real.exp (-(1 / σ))) (Icc 1 T) := by
      intro x hx
      have : x ≠ 0 := by linarith [hx.1]
      exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
    have e2 : ∫⁻ σ in Ioc 1 T, ENNReal.ofReal (1 - Real.exp (-sOpt T σ)) =
        ENNReal.ofReal (∫ σ in (1:ℝ)..T, (1 - Real.exp (-(1 / σ)))) := by
      rw [setLIntegral_congr_fun measurableSet_Ioc
        (g := fun σ => ENNReal.ofReal (1 - Real.exp (-(1 / σ))))]
      · rw [intervalIntegral.integral_of_le hT.le, ofReal_integral_eq_lintegral_ofReal]
        · exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        · refine ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => ?_
          have := Real.exp_le_one_iff.2 (show -(1/σ) ≤ 0 by
            have : 0 < σ := by linarith [hσ.1]
            simp; positivity)
          simp only [Pi.zero_apply]; linarith
      · intro x hx; simp only [sOpt, if_neg (not_le.2 hx.1), if_pos hx.2]
    have e3 : ∫⁻ σ in Ioi T, ENNReal.ofReal (1 - Real.exp (-sOpt T σ)) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)]
      · simp
      · intro x hx
        have hx' : T < x := hx
        simp [sOpt, if_neg (not_le.2 (lt_trans hT hx')), if_neg (not_le.2 hx')]
    have hroot' : ∫ σ in (1:ℝ)..T, (1 - Real.exp (-(1 / σ))) = Real.exp (-1) := by
      unfold frRootEq at hroot; linarith
    calc ∫⁻ τ in Ici 0, ENNReal.ofReal (1 - Real.exp (-sOpt T τ))
        ≤ ∫⁻ τ in (Icc 0 1 ∪ Ioc 1 T) ∪ Ioi T, ENNReal.ofReal (1 - Real.exp (-sOpt T τ)) :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ τ in Icc 0 1, ENNReal.ofReal (1 - Real.exp (-sOpt T τ))) +
            (∫⁻ τ in Ioc 1 T, ENNReal.ofReal (1 - Real.exp (-sOpt T τ))) +
            ∫⁻ τ in Ioi T, ENNReal.ofReal (1 - Real.exp (-sOpt T τ)) := by
          refine (lintegral_union_le _ _ _).trans ?_
          gcongr
          exact lintegral_union_le _ _ _
      _ = 1 := by
          rw [e1, e2, e3, add_zero, hroot', ← ENNReal.ofReal_add, sub_add_cancel,
            ENNReal.ofReal_one]
          · have := Real.exp_le_one_iff.2 (show (-1:ℝ) ≤ 0 by norm_num); linarith
          · exact (Real.exp_pos _).le

lemma sOpt_obj_ge (T : ℝ) (hT : 1 < T) :
    ENNReal.ofReal (1 + Real.log T) ≤ frObj (sOpt T) := by
  unfold frObj
  have hdisj : Disjoint (Icc (0:ℝ) 1) (Ioc 1 T) := by
    rw [Set.disjoint_left]; intro x hx hx'; linarith [hx.2, hx'.1]
  have e1 : ∫⁻ σ in Icc 0 1, ENNReal.ofReal (sOpt T σ) = ENNReal.ofReal 1 := by
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => ENNReal.ofReal 1)]
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
    · intro x hx; simp only [sOpt, if_pos hx.2]
  have hcont : ContinuousOn (fun σ : ℝ => 1 / σ) (Icc 1 T) := by
    intro x hx
    have : x ≠ 0 := by linarith [hx.1]
    exact (by fun_prop (disch := assumption) : ContinuousAt _ x).continuousWithinAt
  have e2 : ∫⁻ σ in Ioc 1 T, ENNReal.ofReal (sOpt T σ) = ENNReal.ofReal (Real.log T) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun σ => ENNReal.ofReal (1 / σ))]
    · have hlog : ∫ σ in (1:ℝ)..T, 1 / σ = Real.log T := by
        rw [integral_one_div, div_one]
        intro h0
        rw [Set.uIcc_of_le hT.le] at h0
        linarith [h0.1]
      rw [← hlog, intervalIntegral.integral_of_le hT.le, ofReal_integral_eq_lintegral_ofReal]
      · exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => ?_
        have : 0 < σ := by linarith [hσ.1]
        simp only [Pi.zero_apply]; positivity
    · intro x hx; simp only [sOpt, if_neg (not_le.2 hx.1), if_pos hx.2]
  calc ENNReal.ofReal (1 + Real.log T)
      = (∫⁻ σ in Icc 0 1, ENNReal.ofReal (sOpt T σ)) + ∫⁻ σ in Ioc 1 T, ENNReal.ofReal (sOpt T σ) := by
        rw [e1, e2, ENNReal.ofReal_add zero_le_one (Real.log_nonneg hT.le)]
    _ = ∫⁻ σ in Icc 0 1 ∪ Ioc 1 T, ENNReal.ofReal (sOpt T σ) :=
        (lintegral_union measurableSet_Ioc hdisj).symm
    _ ≤ ∫⁻ σ in Ici 0, ENNReal.ofReal (sOpt T σ) := by
        apply lintegral_mono_set
        intro x hx
        rcases hx with hx | hx
        · exact hx.1
        · exact le_of_lt (lt_trans zero_lt_one hx.1)

end SPPFRV

theorem solution (T : ℝ) (hT : 1 < T) (hroot : frRootEq T) :
    IsGreatest {x : ℝ≥0∞ | ∃ s : ℝ → ℝ, FRFeasible s ∧ x = frObj s}
        (ENNReal.ofReal (1 + Real.log T)) ∧
      1 + Real.log T ≤ 15283 / 10000 := by
  refine ⟨⟨⟨SPPFRV.sOpt T, SPPFRV.sOpt_feasible T hT hroot, le_antisymm
      (SPPFRV.sOpt_obj_ge T hT)
      (SPPFRV.upper T hT hroot _ (SPPFRV.sOpt_feasible T hT hroot))⟩, ?_⟩, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    exact SPPFRV.upper T hT hroot s hs
  · have h := SPPFRV.root_le T hT hroot
    have : Real.log T ≤ 5283 / 10000 := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact h
    linarith
