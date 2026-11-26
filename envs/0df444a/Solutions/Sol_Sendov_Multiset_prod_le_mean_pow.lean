-- Prove2me | solution 1 for Sendov.Multiset.prod_le_mean_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:58.957847+00:00
-- url     : https://prove2.me/submissions/9010e3f4-67b5-4184-8211-04fde6b5ff58

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Maclaurin
import Theorems.Thm_Sendov_amgm_step

set_option autoImplicit false
open Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}
namespace Sendov
namespace Multiset
theorem _root_.solution : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) →
    s.prod ≤ (s.sum / s.card) ^ s.card := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro hs
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have hIH := ih ht
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.prod_cons, Nat.cast_add,
      Nat.cast_one]
    rcases Nat.eq_zero_or_pos t.card with hc | hc
    · -- `t` is empty
      have ht0 : t = 0 := Multiset.card_eq_zero.1 hc
      subst ht0
      simp
    · have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0` forces `t.prod = 0`
        have hzero : t.prod = 0 := by
          have : t.prod ≤ u ^ t.card := hIH
          rw [← hz] at this
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [h0] at this
          linarith
        rw [hzero, mul_zero]
        positivity
      · have hstep := amgm_step (a := a) t.card hupos ha
        calc a * t.prod ≤ a * u ^ t.card := mul_le_mul_of_nonneg_left hIH ha
          _ ≤ ((a + t.card * u) / (t.card + 1)) ^ (t.card + 1) := hstep
          _ = ((a + t.sum) / (t.card + 1)) ^ (t.card + 1) := by rw [hsum]
end Multiset
end Sendov
