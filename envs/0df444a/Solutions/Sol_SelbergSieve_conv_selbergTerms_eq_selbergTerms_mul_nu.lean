-- Prove2me | solution 1 for SelbergSieve.conv_selbergTerms_eq_selbergTerms_mul_nu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:17:38.559554+00:00
-- url     : https://prove2.me/submissions/6560bc6e-306d-4bcb-84a0-ec7b8c66e2ce

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Theorems.Thm_Aux_div_mult_of_dvd_squarefree
import Theorems.Thm_Aux_sum_over_dvd_ite
import Theorems.Thm_SelbergSieve_nu_eq_conv_one_div_selbergTerms

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

open SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound

local notation3 "g" => SelbergSieve.selbergTerms s

local notation "δ" => delta

-- Unused ?

-- Facts about g

open SelbergSieve in
theorem solution {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x,
        Nat.sum_divisorsAntidiagonal' fun x _ => g x, sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g (selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply SelbergSieve.selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

-- Results about Lambda Squared Sieves

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s
