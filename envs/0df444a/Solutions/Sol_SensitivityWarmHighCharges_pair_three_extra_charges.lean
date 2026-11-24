-- Prove2me | solution 1 for SensitivityWarmHighCharges.pair_three_extra_charges
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:58.642938+00:00
-- url     : https://prove2.me/submissions/541e7d46-7b09-4007-8e19-e8d01e6c8085

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityWarmHighCharges
end SensitivityWarmHighCharges


/-! Zero, one, or two receiving physical children add zero, one maximum,
or two downward prices to a warm head's own and soft-guard base price. -/
open SensitivityWarmHighCharges
open scoped Classical BigOperators
set_option autoImplicit false

theorem solution {I J : Type} [DecidableEq I]
    (scale : ℝ) (hscale : 0 ≤ scale) (own incoming : Bool → Finset I) (extra : Finset J)
    (base left right kind hits : ℕ) (hhits : hits ≤ 2) (cf : Array ℕ)
    (hbase : (∑ side : Bool, ((own side).card : ℝ)) + (extra.card : ℝ) ≤ scale*(base : ℕ))
    (hleft : ((incoming false).card : ℝ) ≤ scale*(left : ℕ))
    (hright : ((incoming true).card : ℝ) ≤ scale*(right : ℕ))
    (hzero : hits = 0 → ∀ side, incoming side = ∅)
    (hone : hits ≤ 1 → ∃ side : Bool, incoming (!side) = ∅)
    (hc0 : base ≤ cf[3*kind]?.getD 0)
    (hc1 : base + max left right ≤ cf[3*kind+1]?.getD 0)
    (hc2 : base + left + right ≤ cf[3*kind+2]?.getD 0) :
    (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) + (extra.card : ℝ) ≤
      scale*(cf[3*kind+hits]?.getD 0 : ℕ) := by
  have hsplit : (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) + (extra.card : ℝ) ≤
      ((∑ side : Bool, ((own side).card : ℝ)) + (extra.card : ℝ)) +
        ∑ side : Bool, ((incoming side).card : ℝ) := by
    have h := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset Bool)) =>
      Nat.cast_le (α := ℝ).mpr (Finset.card_union_le (own side) (incoming side)))
    simp only [Nat.cast_add,Finset.sum_add_distrib] at h
    linarith
  have hu : (Finset.univ : Finset Bool) = {false,true} := by decide
  have hsum : (∑ side : Bool, ((incoming side).card : ℝ)) =
      ((incoming false).card : ℝ) + ((incoming true).card : ℝ) := by simp [hu]
  have hfee (fee : ℕ) (hfee : (∑ side : Bool, ((incoming side).card : ℝ)) ≤ scale*(fee : ℕ))
      (hcf : base+fee ≤ cf[3*kind+hits]?.getD 0) :
      (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) + (extra.card : ℝ) ≤
        scale*(cf[3*kind+hits]?.getD 0 : ℕ) := by
    have hbound := hsplit.trans (add_le_add hbase hfee)
    have hscale := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).mpr hcf) hscale
    rw [Nat.cast_add,mul_add] at hscale
    exact hbound.trans hscale
  interval_cases hits
  · apply hfee 0
    · simp only [hzero rfl,Finset.card_empty,Nat.cast_zero,Finset.sum_const_zero,mul_zero,le_refl]
    · simpa only [Nat.add_zero] using hc0
  · apply hfee (max left right)
    · obtain ⟨side,he⟩ := hone (by decide)
      rw [hsum]
      cases side
      · change incoming true = ∅ at he
        rw [he,Finset.card_empty,Nat.cast_zero,add_zero]
        exact hleft.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (le_max_left _ _)) hscale)
      · change incoming false = ∅ at he
        rw [he,Finset.card_empty,Nat.cast_zero,zero_add]
        exact hright.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (le_max_right _ _)) hscale)
    · exact hc1
  · apply hfee (left+right)
    · rw [hsum,Nat.cast_add,mul_add]
      exact add_le_add hleft hright
    · simpa only [Nat.add_assoc] using hc2
