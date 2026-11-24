-- Prove2me | solution 1 for TaoFivePrimes.centredVaughan_smoothedMangoldt_identity
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T20:38:13.131988+00:00
-- url     : https://prove2.me/submissions/483055c0-19d9-491b-a450-bf6b8688edba

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
import Definitions.Def_TaoFivePrimes_TypeISlabSums
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Theorems.Thm_TaoFivePrimes_sum_dirichlet_pairing

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators
open ArithmeticFunction Finset

namespace TaoFivePrimes

open TypeIOuterDAssembly

private lemma restrictLE_add_restrictGT_eq (B : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticRestrictLE B f + arithmeticRestrictGT B f = f := by
  ext n
  change (if n ≤ B then f n else 0) + (if B < n then f n else 0) = f n
  by_cases h : n ≤ B
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (Nat.lt_of_not_le h), zero_add]

private lemma log_eq_restrict (V : ℕ) :
    ArithmeticFunction.log
      = arithmeticRestrictLE V ArithmeticFunction.log
        + arithmeticRestrictGT V ArithmeticFunction.log :=
  (restrictLE_add_restrictGT_eq V ArithmeticFunction.log).symm

private lemma restrictGT_log_eq_two_halfLog (V : ℕ) :
    arithmeticRestrictGT V ArithmeticFunction.log
      = vaughanTruncatedHalfLog V + vaughanTruncatedHalfLog V := by
  ext n
  change (if V < n then ArithmeticFunction.log n else 0)
      = (if V < n then (1 / 2 : ℝ) * ArithmeticFunction.log n else 0)
        + (if V < n then (1 / 2 : ℝ) * ArithmeticFunction.log n else 0)
  by_cases h : V < n
  · simp only [if_pos h]
    ring
  · simp only [if_neg h]
    ring

private lemma restrictLE_mu_eq_sub (U : ℕ) :
    arithmeticRestrictLE U (μ : ArithmeticFunction ℝ)
      = (μ : ArithmeticFunction ℝ) - arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) := by
  rw [eq_sub_iff_add_eq]
  exact restrictLE_add_restrictGT_eq U (μ : ArithmeticFunction ℝ)

/-- Arithmetic-function form of the von Mangoldt identity: the centred Vaughan Type I
part plus the transferred half-log block plus the low-`w` Möbius-log block plus the
correction coefficient applied to `ζ` recovers `Λ`. -/
theorem vaughanTypeIPart_add_vaughan_blocks_eq_vonMangoldt (U V : ℕ) :
    vaughanTypeIPart U V
      + (arithmeticRestrictGT U (μ : ArithmeticFunction ℝ)) * vaughanTruncatedHalfLog V
      + (arithmeticRestrictGT U (μ : ArithmeticFunction ℝ))
          * arithmeticRestrictLE V ArithmeticFunction.log
      + (vaughanTypeICorrectionCoefficient U V) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      = (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  have hsplit : vaughanTypeIPart U V
      = (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
        - arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
        - (vaughanTypeICorrectionCoefficient U V) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
        + arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * vaughanTruncatedHalfLog V := by
    unfold vaughanTypeIPart vaughanTypeICorrectionCoefficient
    rw [restrictLE_mu_eq_sub U, sub_mul]
  have hlogsplit : arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log
      = arithmeticRestrictGT U (μ : ArithmeticFunction ℝ)
          * arithmeticRestrictLE V ArithmeticFunction.log
        + arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * vaughanTruncatedHalfLog V
        + arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * vaughanTruncatedHalfLog V := by
    have h1 := congrArg (fun f : ArithmeticFunction ℝ =>
      arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * f) (log_eq_restrict V)
    rw [h1, mul_add, restrictGT_log_eq_two_halfLog V, mul_add]
    abel
  have hmain : vaughanTypeIPart U V
      = (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
        - arithmeticRestrictGT U (μ : ArithmeticFunction ℝ)
            * arithmeticRestrictLE V ArithmeticFunction.log
        - arithmeticRestrictGT U (μ : ArithmeticFunction ℝ) * vaughanTruncatedHalfLog V
        - (vaughanTypeICorrectionCoefficient U V)
            * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    rw [hsplit, ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, hlogsplit]
    abel
  rw [hmain]
  abel

/-- `eta0VaughanTest` vanishes past the cutoff. -/
private lemma eta0VaughanTest_eq_zero_of_lt {x alpha : ℝ} {n : ℕ} (h : x < n) :
    eta0VaughanTest x alpha n = 0 := by
  have hEta : eta0 ((n : ℝ) / x) = 0 := by
    unfold eta0
    split_ifs with hpos
    · have hxpos : 0 < x := by
        by_contra hx
        rw [not_lt] at hx
        rcases lt_or_eq_of_le hx with hx' | rfl
        · exact absurd hpos (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_lt hx')))
        · simp at hpos
      have h1 : 1 < (n : ℝ) / x := (one_lt_div hxpos).mpr h
      have hlog : Real.log 2 < |Real.log (2 * ((n : ℝ) / x))| := by
        rw [abs_of_pos (Real.log_pos (by linarith))]
        exact Real.log_lt_log (by norm_num) (by linarith)
      rw [max_eq_left (by linarith : Real.log 2 - |Real.log (2 * ((n : ℝ) / x))| ≤ 0)]
      ring
    · rfl
  unfold eta0VaughanTest
  rw [hEta]
  by_cases h : n.Coprime 2 <;> simp [h]

/-- **Smoothed von Mangoldt identity.** The centred Vaughan Type I sum plus the
transferred half-log block plus the low-`w` Möbius-log block plus the correction
coefficient applied to `ζ` equals the smoothed odd von Mangoldt sum. -/
theorem eta0VaughanTypeISum_add_vaughan_blocks_eq_vonMangoldtSum
    (x alpha U V : ℝ) :
    eta0VaughanTypeISum x alpha U V
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
                * vaughanTruncatedHalfLog ⌊V⌋₊) n : ℝ) : ℂ)
            * eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
                * arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.log) n : ℝ) : ℂ)
            * eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊)
                * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * eta0VaughanTest x alpha n))
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * eta0VaughanTest x alpha n) := by
  rw [eta0VaughanTypeISum, arithmeticWeightedSum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hn := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughanTypeIPart_add_vaughan_blocks_eq_vonMangoldt ⌊U⌋₊ ⌊V⌋₊)
  simp only [ArithmeticFunction.add_apply] at hn
  rw [← hn]
  push_cast
  ring



open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction Finset

set_option autoImplicit false
set_option maxRecDepth 10000

/-- `eta0` vanishes to the left of `1/4`. -/
private lemma eta0_eq_zero_of_le_quarter {t : ℝ} (h : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · rw [max_eq_left]
    · ring
    · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      have habs : Real.log 2 ≤ |Real.log (2 * t)| :=
        le_trans (by linarith [hlog, hloghalf]) (neg_le_abs _)
      linarith
  · rfl

/-- `eta0` vanishes at and to the right of `1`. -/
private lemma eta0_eq_zero_of_one_le {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · rw [max_eq_left]
    · ring
    · have habs : Real.log 2 ≤ |Real.log (2 * t)| := by
        rw [abs_of_pos (Real.log_pos (by linarith : (1 : ℝ) < 2 * t))]
        exact Real.log_le_log (by norm_num) (by linarith)
      linarith
  · rfl

private lemma eta0VaughanTest_eq_zero_of_not_coprime_two {x alpha : ℝ} {n : ℕ}
    (h : ¬ n.Coprime 2) : eta0VaughanTest x alpha n = 0 := by
  unfold eta0VaughanTest
  rw [if_neg h]

private lemma eta0VaughanTest_eq_zero_of_x_le {x alpha : ℝ} {n : ℕ} (hx0 : 0 < x)
    (h : x ≤ n) : eta0VaughanTest x alpha n = 0 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact eta0VaughanTest_eq_zero_of_lt hlt
  · have hEta : eta0 ((n : ℝ) / x) = 0 := by
      have hone : (n : ℝ) / x = 1 := by
        rw [← heq, div_self hx0.ne']
      rw [hone]
      exact eta0_eq_zero_of_one_le le_rfl
    unfold eta0VaughanTest
    rw [hEta]
    by_cases hc : n.Coprime 2 <;> simp [hc]

/-- **Bridge to the transferred slab sum.** The Möbius-weighted truncated
half-logarithm Dirichlet convolution, summed against the eta-zero test, is
exactly the transferred half-logarithmic block `typeISlabS3`. -/
theorem sum_vaughanTruncatedHalfLog_eq_typeISlabS3
    (x alpha U V : ℝ) (hx0 : 0 < x) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (((((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
              * vaughanTruncatedHalfLog ⌊V⌋₊) n : ℝ) : ℂ)
          * eta0VaughanTest x alpha n))
      = typeISlabS3 x alpha U V := by
  classical
  have hxN : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one x
  have hF : ∀ n, ⌊x⌋₊ + 1 ≤ n → eta0VaughanTest x alpha n = 0 := by
    intro n hn
    exact eta0VaughanTest_eq_zero_of_lt (lt_of_lt_of_le hxN (by exact_mod_cast hn))
  rw [sum_dirichlet_pairing (arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
        (vaughanTruncatedHalfLog ⌊V⌋₊) (eta0VaughanTest x alpha) (⌊x⌋₊ + 1) hF]
  have hpoint : ∀ d w : ℕ,
      (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ)) d : ℝ) : ℂ)
          * (((vaughanTruncatedHalfLog ⌊V⌋₊) w : ℝ) : ℂ)
          * eta0VaughanTest x alpha (d * w)
        = (if ⌊U⌋₊ < d then
            (if ⌊V⌋₊ < w then
              (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                * eta0VaughanTest x alpha (d * w)
            else 0)
          else 0) := by
    intro d w
    unfold vaughanTruncatedHalfLog vaughanHalfLog arithmeticRestrictGT
    by_cases hd : ⌊U⌋₊ < d <;> by_cases hw : ⌊V⌋₊ < w <;> simp [hd, hw] <;> ring
  have hLHS : (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
        (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ)) d : ℝ) : ℂ)
          * (((vaughanTruncatedHalfLog ⌊V⌋₊) w : ℝ) : ℂ)
          * eta0VaughanTest x alpha (d * w))
      = ∑ d ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun d => ⌊U⌋₊ < d),
          ∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
            (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
              * eta0VaughanTest x alpha (d * w) := by
    calc (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
          (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ)) d : ℝ) : ℂ)
            * (((vaughanTruncatedHalfLog ⌊V⌋₊) w : ℝ) : ℂ)
            * eta0VaughanTest x alpha (d * w))
        = ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
            (if ⌊U⌋₊ < d then
              (if ⌊V⌋₊ < w then
                (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                  * eta0VaughanTest x alpha (d * w)
              else 0)
            else 0) := by
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun w _ => hpoint d w))
      _ = ∑ d ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun d => ⌊U⌋₊ < d),
            ∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
              (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                * eta0VaughanTest x alpha (d * w) := by
          have h2 : ∀ d : ℕ,
              (∑ w ∈ Finset.range (⌊x⌋₊ + 1),
                  if ⌊U⌋₊ < d then
                    (if ⌊V⌋₊ < w then
                      (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                        * eta0VaughanTest x alpha (d * w)
                    else 0)
                  else 0)
                = (if ⌊U⌋₊ < d then
                    (∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
                      (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                        * eta0VaughanTest x alpha (d * w))
                  else 0) := by
            intro d
            by_cases hd : ⌊U⌋₊ < d
            · simp only [hd, if_true]
              rw [Finset.sum_ite]
              simp
            · simp [hd]
          calc (∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
                (if ⌊U⌋₊ < d then
                  (if ⌊V⌋₊ < w then
                    (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                      * eta0VaughanTest x alpha (d * w)
                  else 0)
                else 0))
              = ∑ d ∈ Finset.range (⌊x⌋₊ + 1),
                  (if ⌊U⌋₊ < d then
                    (∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
                      (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                        * eta0VaughanTest x alpha (d * w))
                  else 0) :=
                Finset.sum_congr rfl (fun d _ => h2 d)
            _ = ∑ d ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun d => ⌊U⌋₊ < d),
                  ∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
                    (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
                      * eta0VaughanTest x alpha (d * w) := by
                rw [Finset.sum_ite]
                simp
  rw [hLHS]
  simp only [typeISlabS3, typeISlabK, transferredInnerSupport, fullInnerSupport,
    theorem51Divisors]
  have hsub : ((Finset.Icc 1 ⌊U * V⌋₊).filter (fun d => d.Coprime 2)).filter
        (fun d => ⌊U⌋₊ < d)
      ⊆ (Finset.range (⌊x⌋₊ + 1)).filter (fun d => ⌊U⌋₊ < d) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdD, hdU⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hdD
    obtain ⟨⟨hd1, hdUV⟩, _⟩ := hdD
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, hdU⟩
    have h1 : (d : ℝ) ≤ U * V :=
      le_trans (by exact_mod_cast hdUV) (Nat.floor_le (mul_nonneg hU0 hV0))
    have h2 : (d : ℝ) < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one x]
    exact_mod_cast h2
  have hzero : ∀ d ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun d => ⌊U⌋₊ < d),
      d ∉ ((Finset.Icc 1 ⌊U * V⌋₊).filter (fun d => d.Coprime 2)).filter
        (fun d => ⌊U⌋₊ < d) →
      (∑ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
          (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
            * eta0VaughanTest x alpha (d * w)) = 0 := by
    intro d hd hdNot
    rw [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨_, hdU⟩ := hd
    refine Finset.sum_eq_zero (fun w hw => ?_)
    rw [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨_, hwV⟩ := hw
    have htest : eta0VaughanTest x alpha (d * w) = 0 := by
      by_cases hcop : (d * w).Coprime 2
      · have hdcop : d.Coprime 2 := ((Nat.coprime_mul_iff_left).mp hcop).1
        have hd1 : 1 ≤ d := by
          rcases Nat.eq_zero_or_pos d with h0 | hpos
          · subst h0
            simp [Nat.coprime_zero_left] at hdcop
          · exact hpos
        have hdnotD : d ∉ (Finset.Icc 1 ⌊U * V⌋₊).filter (fun d => d.Coprime 2) :=
          fun hmem => hdNot (by
            rw [Finset.mem_filter]
            exact ⟨hmem, hdU⟩)
        have hdgtUV : ⌊U * V⌋₊ < d := by
          by_cases hmem : d ∈ Finset.Icc 1 ⌊U * V⌋₊
          · exact absurd (Finset.mem_filter.mpr ⟨hmem, hdcop⟩) hdnotD
          · by_contra hcon
            push_neg at hcon
            exact hmem (Finset.mem_Icc.mpr ⟨hd1, hcon⟩)
        have hw1 : ⌊V⌋₊ + 1 ≤ w := Nat.succ_le_of_lt hwV
        have hd1' : ⌊U * V⌋₊ + 1 ≤ d := Nat.succ_le_of_lt hdgtUV
        have hprod : U * V ^ 2
            < (((⌊U * V⌋₊ + 1 : ℕ) : ℝ) * ((⌊V⌋₊ + 1 : ℕ) : ℝ)) := by
          have h1 : U * V < ((⌊U * V⌋₊ + 1 : ℕ) : ℝ) := by
            push_cast
            exact Nat.lt_floor_add_one (U * V)
          have h2 : V ≤ ((⌊V⌋₊ + 1 : ℕ) : ℝ) := by
            push_cast
            exact le_of_lt (Nat.lt_floor_add_one V)
          have h3 : (0 : ℝ) < ((⌊V⌋₊ + 1 : ℕ) : ℝ) := by positivity
          have h4 : U * V ^ 2 ≤ U * V * ((⌊V⌋₊ + 1 : ℕ) : ℝ) := by
            rw [show U * V ^ 2 = U * V * V by ring]
            exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hU0 hV0)
          have h5 : U * V * ((⌊V⌋₊ + 1 : ℕ) : ℝ)
              < ((⌊U * V⌋₊ + 1 : ℕ) : ℝ) * ((⌊V⌋₊ + 1 : ℕ) : ℝ) :=
            mul_lt_mul_of_pos_right h1 h3
          linarith
        have hdw : ((⌊U * V⌋₊ + 1 : ℕ) : ℝ) * ((⌊V⌋₊ + 1 : ℕ) : ℝ) ≤ (d * w : ℕ) := by
          have hmul := Nat.mul_le_mul hd1' hw1
          exact_mod_cast hmul
        exact eta0VaughanTest_eq_zero_of_lt
          (lt_of_le_of_lt hUV2 (lt_of_lt_of_le hprod hdw))
      · exact eta0VaughanTest_eq_zero_of_not_coprime_two hcop
    rw [htest]
    ring
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdD, hdU⟩ := hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hdD
  obtain ⟨⟨hd1, hdUV⟩, hdcop⟩ := hdD
  rw [Finset.mul_sum]
  have hsubW : (fullInnerSupport x d).filter (fun w => ⌊V⌋₊ < w)
      ⊆ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwfull, hwV⟩ := hw
    rw [fullInnerSupport, Finset.mem_filter] at hwfull
    obtain ⟨hwIoc, hwPair⟩ := hwfull
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, hwV⟩
    have hdw : d * w ≤ ⌊x⌋₊ := (Finset.mem_filter.mp hwPair).2.1
    have hdcop' : d.Coprime 2 := (Finset.mem_filter.mp hwPair).2.2.1
    have hd1' : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0
        simp [Nat.coprime_zero_left] at hdcop'
      · exact hpos
    have hle : w ≤ d * w := Nat.le_mul_of_pos_left w hd1'
    omega
  have hzeroW : ∀ w ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun w => ⌊V⌋₊ < w),
      w ∉ (fullInnerSupport x d).filter (fun w => ⌊V⌋₊ < w) →
      (((μ d : ℝ) : ℂ) * (((1 / 2 : ℝ) * Real.log (w : ℝ) : ℝ) : ℂ))
        * eta0VaughanTest x alpha (d * w) = 0 := by
    intro w hw hwNot
    rw [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwltM, hwV⟩ := hw
    have hdlx : d ≤ ⌊x⌋₊ := Nat.le_floor (by
      have h1 : (d : ℝ) ≤ U * V :=
        le_trans (by exact_mod_cast hdUV) (Nat.floor_le (mul_nonneg hU0 hV0))
      linarith [hx0])
    have htest : eta0VaughanTest x alpha (d * w) = 0 := by
      by_cases hcop : (d * w).Coprime 2
      · have hdcopw : d.Coprime 2 := ((Nat.coprime_mul_iff_left).mp hcop).1
        have hwcop : w.Coprime 2 := ((Nat.coprime_mul_iff_left).mp hcop).2
        have hwIoc : w ∈ Finset.Ioc 0 ⌊x⌋₊ := by
          rw [Finset.mem_Ioc]
          exact ⟨by omega, by omega⟩
        have hnot : ¬ (d * w ≤ ⌊x⌋₊ ∧ d.Coprime 2 ∧ w.Coprime 2
            ∧ x / 4 < ((d * w : ℕ) : ℝ) ∧ ((d * w : ℕ) : ℝ) < x) := by
          intro hcond
          refine hwNot ?_
          rw [Finset.mem_filter]
          refine ⟨?_, hwV⟩
          rw [fullInnerSupport, Finset.mem_filter]
          refine ⟨hwIoc, ?_⟩
          rw [eta0VaughanOpenOddPairs, Finset.mem_filter]
          exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨hd1, hdlx⟩, hwIoc⟩, hcond⟩
        have hdisj : ¬ (d * w ≤ ⌊x⌋₊) ∨ ¬ d.Coprime 2 ∨ ¬ w.Coprime 2
            ∨ ¬ (x / 4 < ((d * w : ℕ) : ℝ)) ∨ ¬ (((d * w : ℕ) : ℝ) < x) := by
          by_contra hcon
          push_neg at hcon
          exact hnot hcon
        have hEta : eta0 (((d * w : ℕ) : ℝ) / x) = 0 := by
          rcases hdisj with h | h | h | h | h
          · apply eta0_eq_zero_of_one_le
            rw [le_div_iff₀ hx0]
            have h1 : ⌊x⌋₊ + 1 ≤ d * w := Nat.succ_le_of_lt (Nat.lt_of_not_le h)
            have h3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((d * w : ℕ) : ℝ) := by
              exact_mod_cast h1
            linarith [Nat.lt_floor_add_one x]
          · exact absurd hdcopw h
          · exact absurd hwcop h
          · apply eta0_eq_zero_of_le_quarter
            rw [div_le_iff₀ hx0]
            linarith
          · apply eta0_eq_zero_of_one_le
            rw [le_div_iff₀ hx0]
            linarith
        unfold eta0VaughanTest
        rw [if_pos hcop, hEta]
        simp
      · exact eta0VaughanTest_eq_zero_of_not_coprime_two hcop
    rw [htest]
    ring
  rw [← Finset.sum_subset hsubW hzeroW]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  push_cast
  ring

/-- **Sharp smoothed identity in slab form.** The centred Vaughan Type I sum,
the transferred half-log slab sum `typeISlabS3`, the low-`w` Möbius-log block
and the correction coefficient block sum to the smoothed odd von Mangoldt sum. -/
theorem eta0VaughanTypeISum_add_typeISlabS3_add_blocks_eq_vonMangoldtSum
    (x alpha U V : ℝ) (hx0 : 0 < x) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    eta0VaughanTypeISum x alpha U V + typeISlabS3 x alpha U V
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
                * arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.log) n : ℝ) : ℂ)
            * eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊)
                * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * eta0VaughanTest x alpha n))
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * eta0VaughanTest x alpha n) := by
  rw [← sum_vaughanTruncatedHalfLog_eq_typeISlabS3 x alpha U V hx0 hU0 hV0 hUVx hUV2]
  exact eta0VaughanTypeISum_add_vaughan_blocks_eq_vonMangoldtSum x alpha U V

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x alpha U V : ℝ) :
    TaoFivePrimes.eta0VaughanTypeISum x alpha U V
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
                * TaoFivePrimes.vaughanTruncatedHalfLog ⌊V⌋₊) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.arithmeticRestrictGT ⌊U⌋₊ (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
                * TaoFivePrimes.arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.log) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      + (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊)
                * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * TaoFivePrimes.eta0VaughanTest x alpha n))
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha n)
  := TaoFivePrimes.eta0VaughanTypeISum_add_vaughan_blocks_eq_vonMangoldtSum x alpha U V
