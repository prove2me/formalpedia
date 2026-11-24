-- Prove2me | solution 1 for QuadraticProbe717.Insertion.distinct_square_probes
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:28:51.928487+00:00
-- url     : https://prove2.me/submissions/8f321d3e-bebf-42e0-9c0c-b88dcd1e6cc4

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open QuadraticProbe717.Insertion

theorem solution (n : ℕ) (hn : n.Prime) (k : ℕ)
    (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    Function.Injective (fun a : Fin k => (a.val : ZMod n)^2) := by
  have := Fact.mk hn
  intro a b hab
  simp only at hab
  have h : ((a.val : ZMod n) - b.val) * ((a.val : ZMod n) + b.val) = 0 := by
    linear_combination hab
  rcases mul_eq_zero.mp h with h1 | h2
  · -- a ≡ b (mod n) with a, b < n
    have ha : a.val < n := by omega
    have hb : b.val < n := by omega
    have : ((a.val : ℕ) : ZMod n) = ((b.val : ℕ) : ZMod n) := sub_eq_zero.mp h1
    rw [ZMod.natCast_eq_natCast_iff' ] at this
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact Fin.ext this
  · -- a + b ≡ 0 (mod n) with a + b < n forces a = b = 0
    have hs : a.val + b.val < n := by omega
    have : ((a.val + b.val : ℕ) : ZMod n) = 0 := by push_cast; exact h2
    rw [ZMod.natCast_eq_zero_iff] at this
    have hz : a.val + b.val = 0 := Nat.eq_zero_of_dvd_of_lt this hs
    exact Fin.ext (by omega)
