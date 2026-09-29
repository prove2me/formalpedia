-- Prove2me | solution 1 for Sieve.rem_sum_le_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:23:25.200852+00:00
-- url     : https://prove2.me/submissions/be2d1152-353f-4277-939c-64f835baef5a

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_SelbergBounds_defs
import Definitions.Def_Sieve_Selberg_defs
import Theorems.Thm_Aux_sum_pow_cardDistinctFactors_le_self_mul_log_pow
/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

open Sieve

open CompletelyMultiplicative
open ArithmeticFunction

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

open ArithmeticFunction

open Sieve in
theorem solution (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree
