-- Prove2me | solution 4 for WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T02:48:42.501982+00:00
-- url     : https://prove2.me/submissions/8459d01f-5882-4e35-9cee-dc5b3240970c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_three_odd_primes_of_coarse_arc_error
import Theorems.Thm_Helfgott_actual_major_arc_main_error
import Theorems.Thm_Helfgott_actual_minor_arc_upper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
open Helfgott

namespace Helfgott.CoarseBridgeAux

lemma goldbach_denominator_bounds :
    (2 : ℝ) ≤ 2+9/(196*Real.sqrt (2*Real.pi)) ∧
    2+9/(196*Real.sqrt (2*Real.pi)) ≤ (203/100 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt (2*Real.pi) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)
  have hs : (2 : ℝ) ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  have hsp : 0 < 196*Real.sqrt (2*Real.pi) := by positivity
  constructor
  · have h : 0 ≤ 9/(196*Real.sqrt (2*Real.pi)) := by positivity
    linarith
  · have h : 9/(196*Real.sqrt (2*Real.pi)) ≤ (3/100 : ℝ) := by
      apply (div_le_iff₀ hsp).mpr
      nlinarith
    linarith

lemma goldbachScale_pos (N : ℕ) (hN : 0 < N) : 0 < goldbachScale N := by
  have hd := goldbach_denominator_bounds.1
  unfold goldbachScale
  apply div_pos (by exact_mod_cast hN)
  linarith

lemma goldbachScale_le_relation (N : ℕ) :
    (N : ℝ) ≤ (203/100 : ℝ)*goldbachScale N := by
  have hd := goldbach_denominator_bounds
  have hp : 0 < 2+9/(196*Real.sqrt (2*Real.pi)) := by linarith [hd.1]
  have hx : 0 ≤ goldbachScale N := by unfold goldbachScale; positivity
  have he : goldbachScale N*(2+9/(196*Real.sqrt (2*Real.pi))) = (N : ℝ) := by
    unfold goldbachScale
    exact div_mul_cancel₀ _ hp.ne'
  have h := mul_le_mul_of_nonneg_left hd.2 hx
  rw [he] at h
  simpa only [mul_comm] using h

lemma goldbachScale_analytic_range (N : ℕ) (hN : 10^27 ≤ N) :
    (49 : ℝ)*10^25 ≤ goldbachScale N := by
  have hn : (10 : ℝ)^27 ≤ (N : ℝ) := by exact_mod_cast hN
  have hs := goldbachScale_le_relation N
  linarith


end Helfgott.CoarseBridgeAux

theorem solution (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  exact Helfgott.three_odd_primes_of_coarse_arc_error n hn hodd
    (Helfgott.actual_major_arc_main_error n hn hodd)
    (Helfgott.actual_minor_arc_upper (goldbachScale n)
      (Helfgott.CoarseBridgeAux.goldbachScale_analytic_range n hn))

#print axioms solution
