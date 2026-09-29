-- Prove2me | solution 1 for Sieve.prime_dvd_primorial_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:22:42.92185+00:00
-- url     : https://prove2.me/submissions/e1f01ccc-ed8e-4078-9d49-7ba0855dc77e

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

open Sieve in
theorem solution (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

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
