-- Prove2me | solution 1 for PI.EF.PK.perronTrunc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:41.802061+00:00
-- url     : https://prove2.me/submissions/c13c62ff-487c-4826-bc12-3e0035a122ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Theorems.Thm_PI_EF_PK_one_lt_cLine
import Theorems.Thm_PI_EF_PK_kernel_le_kb
import Theorems.Thm_PI_EF_PK_term_mul_kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries
namespace PI.EF.PK
theorem _root_.solution {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by
  intro a ha u T hu hT
  have hc1 : 1 < cLine u := one_lt_cLine hu
  set c := cLine u with hcdef
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hSs, hSle⟩ := hS u T hu hT
  have ha0 : a 0 = 0 := by
    have h := ha 0
    rw [ArithmeticFunction.map_zero] at h
    exact norm_le_zero_iff.mp h

  have hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    refine Complex.summable_ofReal.mp (h.congr (fun n => ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
  have hterm : ∀ (n : ℕ) (s : ℂ), s.re = c →
      ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
    intro n s hs
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hn
    · subst hn
      simp
    · exact div_le_div_of_nonneg_right (ha n) (by positivity)
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  have hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    apply div_le_div_of_nonneg_left (by positivity) hc0
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos hc0] at h
    exact h

  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n *
      ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c * (u ^ c / c))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_mul]
        exact MeasureTheory.aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        apply Measurable.aestronglyMeasurable
        fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))
    (Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => by
      have hsum : LSeriesSummable a ((c : ℂ) + t * I) :=
        Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))
      exact hsum.hasSum.mul_right _))

  have hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) *
        ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) := by
    have hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
          ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, LSeries.term_zero]
      · have h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
              ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
            a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext t
          exact term_mul_kernel a u hu0 n hn _
        rw [h1, perronK]
        ring
    rw [hfun]
    exact hDC.mul_left _

  have hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) := by
    have h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [ha0]
      · push_neg at hn
        have hlt : u < n := by
          have h1 := Nat.lt_floor_add_one u
          have h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          linarith
        have h3 : ¬ (1 ≤ u / n) := by
          rw [not_le, div_lt_one (by linarith)]
          exact hlt
        simp [h3]
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)
    have h4 : 1 ≤ u / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp [h4]
  have hdiff := hind.sub hG
  rw [← hdiff.tsum_eq]
  calc _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ c * kb T (u / n) := by
        apply tsum_of_norm_bounded hSs.hasSum
        intro n
        rw [← mul_sub, norm_mul]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [ha0]
        · have hy : 0 < u / n := div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          have h1 := kernel_le_kb hK (u / n) c T hy hc0 hT0
          rw [norm_sub_rev] at h1
          rw [mul_assoc]
          exact mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := hSle
end PI.EF.PK
