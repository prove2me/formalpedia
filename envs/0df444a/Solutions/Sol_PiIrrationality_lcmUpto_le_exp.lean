-- Prove2me | solution 1 for PiIrrationality.lcmUpto_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:29:33.442183+00:00
-- url     : https://prove2.me/submissions/f3555bc9-62f7-4af8-8a73-1c6608dedb57

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_MediumPNT

open Filter Asymptotics
open scoped Topology

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop, (Nat.lcmUpto m : ℝ) ≤ Real.exp ((1 + δ) * (m : ℝ)) := by
  have hpsi : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + δ) * x := by
    obtain ⟨c, hc, hO⟩ := MediumPNT
    obtain ⟨C, hC, hbound⟩ := hO.exists_pos
    have ht : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hh := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop
      simpa only [neg_mul, Function.comp_def] using
        tendsto_neg_atTop_atBot.comp (hh.const_mul_atTop hc)
    have he : ∀ᶠ x : ℝ in atTop,
        C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < δ :=
      (show Tendsto (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        atTop (𝓝 0) by simpa using ht.const_mul C).eventually_lt_const hδ
    filter_upwards [hbound.bound, he, eventually_ge_atTop (0 : ℝ)] with x hx he hx0
    have hxp := Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hx0 hxp.le)] at hx
    have hab := le_abs_self (Chebyshev.psi x - x)
    nlinarith
  have h := tendsto_natCast_atTop_atTop.eventually hpsi
  filter_upwards [h] with m hlog
  rw [Chebyshev.psi_eq_log_lcmUpto] at hlog
  have hpos : (0 : ℝ) < Nat.lcmUpto m := by exact_mod_cast Nat.lcmUpto_pos m
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
