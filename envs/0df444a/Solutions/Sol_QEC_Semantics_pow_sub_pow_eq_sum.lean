-- Prove2me | solution 1 for QEC.Semantics.pow_sub_pow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:39:21.56297+00:00
-- url     : https://prove2.me/submissions/a30bb083-089d-4b59-8a37-c3b01f712100

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter

set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]
namespace QEC.Semantics
theorem _root_.solution (x y : A) (n : Nat) :
    x ^ n - y ^ n =
      ∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        x ^ n * x - y ^ n * y =
            x ^ n * (x - y) + (x ^ n - y ^ n) * y := by noncomm_ring
        _ = x ^ n * (x - y) +
            (∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k)) * y := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (n + 1),
            x ^ k * (x - y) * y ^ (n + 1 - 1 - k) := by
              rw [Finset.sum_mul, Finset.sum_range_succ]
              simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
              rw [add_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              have hkn : k < n := Finset.mem_range.mp hk
              rw [mul_assoc (x ^ k * (x - y)), ← pow_succ]
              congr 2
              omega
end QEC.Semantics
