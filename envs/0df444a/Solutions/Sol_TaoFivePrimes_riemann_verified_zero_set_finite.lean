-- Prove2me | solution 1 for TaoFivePrimes.riemann_verified_zero_set_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T02:44:51.576792+00:00
-- url     : https://prove2.me/submissions/8929d4d5-bbb4-4346-bc9b-028e4f4257ab

import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two

set_option autoImplicit false
set_option maxHeartbeats 0

open Complex Set Topology MeasureTheory Real
open Zeta23

noncomputable section

namespace TaoFivePrimesFiniteness

lemma zeta_ne_zero_on_re_zero {s : ℂ} (hre : s.re = 0) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s.im 0 with him | him
  · have hs : s = 0 := Complex.ext (by simpa using hre) (by simpa using him)
    rw [hs, riemannZeta_zero]
    norm_num
  · have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n he
      have hh := congrArg Complex.im he
      simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at hh
      exact him hh
    have hs1 : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [hre, Complex.one_re] at hh
      norm_num at hh
    intro hz
    have hn := riemannZeta_ne_zero_of_one_le_re (s := 1 - s)
      (by simpa only [Complex.sub_re, Complex.one_re, hre, sub_zero] using (le_refl (1 : ℝ)))
    apply hn
    rw [riemannZeta_one_sub hneg hs1, hz, mul_zero]

lemma zeta_ne_zero_on_im_zero_in_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : s.im = 0) : riemannZeta s ≠ 0 := by
  have hnonneg : 0 ≤ s.im := him.ge
  have habs : |s.im| ≤ 2 := by rw [abs_of_nonneg hnonneg, him]; norm_num
  exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two s h0 h1 habs

lemma closed_strip_zeros_eq (T : ℝ) :
    {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T ∧ riemannZeta s = 0} =
      Zeta23.zerosIn 0 T := by
  ext s
  change (0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T ∧ riemannZeta s = 0) ↔
    ((riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1) ∧ 0 < s.im ∧ s.im ≤ T)
  constructor
  · rintro ⟨h0, _h1, him0, himT, hz⟩
    have hr0 : 0 < s.re := by
      by_contra h
      exact zeta_ne_zero_on_re_zero (le_antisymm (not_lt.mp h) h0) hz
    have hr1 : s.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    have hi : 0 < s.im := by
      by_contra h
      exact zeta_ne_zero_on_im_zero_in_strip hr0 hr1 (le_antisymm (not_lt.mp h) him0) hz
    exact ⟨⟨hz, hr0, hr1⟩, hi, himT⟩
  · rintro ⟨⟨hz, hr0, hr1⟩, hi, himT⟩
    exact ⟨hr0.le, hr1.le, hi.le, himT, hz⟩

lemma verified_zero_set_eq (T : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T} =
      Zeta23.zerosIn 0 T := by
  ext s
  constructor
  · rintro ⟨hz, hr0, hr1, hi0, hiT⟩
    rw [← closed_strip_zeros_eq T]
    exact ⟨hr0.le, hr1.le, hi0, hiT, hz⟩
  · rintro ⟨⟨hz, hr0, hr1⟩, hi0, hiT⟩
    exact ⟨hz, hr0, hr1, hi0.le, hiT⟩

theorem verified_zero_set_finite (T : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im ≤ T}.Finite := by
  rw [verified_zero_set_eq]
  exact Zeta23.zetaSeam.finite_window 0 T

end TaoFivePrimesFiniteness

end

theorem solution :
    {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}.Finite :=
  TaoFivePrimesFiniteness.verified_zero_set_finite _
