-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T13:18:45.299234+00:00
-- url     : https://prove2.me/submissions/da71814b-c493-4171-8fca-bebfb0dbcc64

import Theorems.Thm_PrimePairSieve_base_denominator_quadratic_expansion_explicit
import Theorems.Thm_PrimePairSieve_reciprocal_weighted_quadratic_error_certified
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators
set_option autoImplicit false

theorem solution :
    ∃ B E : ℝ, 0 ≤ E ∧ E ≤ (127185 / 154 : ℝ) ∧
      (2 * Real.eulerMascheroniConstant^2 +
        4 * Real.eulerMascheroniConstant *
          (2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
        ((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) -
      (4 * Real.eulerMascheroniConstant +
        4 * (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) +
        Real.log 2) * Real.log 2 + Real.pi ^ 2 / 6 ≤ B) ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (n : ℝ) / z)) -
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) - Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ))) := by
  classical
  rcases PrimePairSieve.base_denominator_quadratic_expansion_explicit with ⟨B, E, hE, hE600, hB, hBase⟩
  let c : ℕ → ℝ := fun n => if Squarefree n then
    ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2 / ((p:ℝ)-2) else 0
  let C : ℝ := TaoFivePrimes.twinPrimeConstant
  let a3 : ℝ := 4 * Real.eulerMascheroniConstant +
    4 * (∑' p : Nat.Primes, Real.log (p:ℝ) / ((p:ℝ)*((p:ℝ)-1))) + Real.log 2
  let B' : ℝ := B - a3*Real.log 2 + Real.pi ^ 2 / 6
  have hc0 : c 0 = 0 := by simp [c]
  have hinput : ∀ t : ℝ, 0 < t →
      |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) -
        ((1/(2*C))*Real.log t^2+(a3/(2*C))*Real.log t+B/(2*C))| ≤
        E*t^(-(1/3:ℝ)) := by
    intro t ht
    have hpoly : (1/(2*C))*Real.log t^2+(a3/(2*C))*Real.log t+B/(2*C) =
        (Real.log t^2+a3*Real.log t+B)/(2*C) := by ring
    rw [hpoly]
    simpa only [c, C, a3] using hBase t ht
  refine ⟨B', (8479/6160)*E, mul_nonneg (by norm_num) hE, ?_, ?_, ?_⟩
  · calc (8479/6160 : ℝ)*E ≤ (8479/6160)*600 :=
          mul_le_mul_of_nonneg_left hE600 (by norm_num)
      _ = 127185/154 := by norm_num
  · dsimp [B', a3]
    linarith [hB]
  · intro z hz
    have h := PrimePairSieve.reciprocal_weighted_quadratic_error_certified
      c hc0 (1/(2*C)) (a3/(2*C)) (B/(2*C)) E hE hinput z hz
    have hcenter :
        (1/(2*C))*Real.log z^2 +
          (a3/(2*C)-2*(1/(2*C))*Real.log 2)*Real.log z +
          B/(2*C)-(a3/(2*C))*Real.log 2+
            (1/(2*C))*Real.pi ^ 2 / 6 =
        (Real.log z^2+(a3-2*Real.log 2)*Real.log z+B')/(2*C) := by
      dsimp [B']
      ring
    rw [hcenter] at h
    have hlinear : a3-2*Real.log 2 =
        4*Real.eulerMascheroniConstant +
          4*(∑' p : Nat.Primes, Real.log (p:ℝ) / ((p:ℝ)*((p:ℝ)-1))) - Real.log 2 := by
      dsimp [a3]
      ring
    rw [hlinear] at h
    simpa only [c, C] using h

#print axioms solution
