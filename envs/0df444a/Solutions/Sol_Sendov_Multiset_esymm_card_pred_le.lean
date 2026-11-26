-- Prove2me | solution 1 for Sendov.Multiset.esymm_card_pred_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:35.815085+00:00
-- url     : https://prove2.me/submissions/4beeaa27-9e44-442b-8e1b-f170fbf9bae8

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Maclaurin
import Theorems.Thm_Sendov_maclaurin_step
import Theorems.Thm_Sendov_Multiset_prod_le_mean_pow
import Theorems.Thm_Sendov_esymm_card_cons

set_option autoImplicit false
open Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}
namespace Sendov
namespace Multiset
theorem _root_.solution : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) → s ≠ 0 →
    s.esymm (s.card - 1) ≤ s.card * (s.sum / s.card) ^ (s.card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons a t ih =>
    intro hs _
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    have hamgm := Multiset.prod_le_mean_pow t ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [Multiset.esymm]
    · have hc : 0 < t.card := Multiset.card_pos.2 ht0
      have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      have hIH := ih ht ht0
      rw [esymm_card_cons a t ht0]
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0`
        have hzero : t.prod = 0 := by
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [← hz, h0] at hamgm
          linarith
        have hsum0 : t.sum = 0 := by rw [hsum, ← hz, mul_zero]
        rw [hzero, hsum0, zero_add, add_zero]
        rcases Nat.lt_or_ge t.card 2 with h1 | h2
        · -- `card t = 1`
          have hc1 : t.card = 1 := by omega
          have he0 : t.esymm (t.card - 1) = 1 := by
            rw [hc1]
            simp [Multiset.esymm]
          rw [he0, hc1]
          norm_num
          linarith
        · -- `card t ≥ 2`
          have hz0 : (0 : ℝ) ^ (t.card - 1) = 0 := zero_pow (by omega)
          rw [← hz, hz0, mul_zero] at hIH
          have : a * t.esymm (t.card - 1) ≤ 0 := by nlinarith [hIH, ha]
          have hrhs : (0 : ℝ) ≤ ((t.card : ℝ) + 1) * (a / ((t.card : ℝ) + 1)) ^ t.card := by
            positivity
          linarith
      · have hstep := maclaurin_step (a := a) t.card hc hupos ha
        calc t.prod + a * t.esymm (t.card - 1)
            ≤ u ^ t.card + a * ((t.card : ℝ) * u ^ (t.card - 1)) := by
              have h2 : a * t.esymm (t.card - 1) ≤ a * ((t.card : ℝ) * u ^ (t.card - 1)) :=
                mul_le_mul_of_nonneg_left hIH ha
              linarith [hamgm]
          _ = u ^ t.card + (t.card : ℝ) * a * u ^ (t.card - 1) := by ring
          _ ≤ ((t.card : ℝ) + 1) * ((a + t.card * u) / (t.card + 1)) ^ t.card := hstep
          _ = ((t.card : ℝ) + 1) * ((a + t.sum) / ((t.card : ℝ) + 1)) ^ t.card := by rw [hsum]
end Multiset
end Sendov
