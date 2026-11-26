-- Prove2me | solution 1 for SensitivityGuardFeeAggregation.aggregate_guard_fees
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:40:22.553198+00:00
-- url     : https://prove2.me/submissions/467d2fcb-42e6-4c85-9b50-9875c46ea021

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardFeeAggregation
end SensitivityGuardFeeAggregation


/-! Exact aggregation of occupied and unoccupied physical guard costs. -/
open SensitivityGuardFeeAggregation
open scoped Classical BigOperators
set_option autoImplicit false


theorem _root_.solution {G : Type} (checks occupied : Finset G)
    (hsub : occupied ⊆ checks) (slots : G → ℕ) (D : ℕ)
    (hslots : ∑ check ∈ checks, slots check = D)
    (fee combined upward : G → ℝ) (baseline : ℝ)
    (hcold : ∀ check ∈ checks, check ∉ occupied → fee check ≤ slots check * baseline)
    (hhot : ∀ check ∈ occupied,
      fee check ≤ combined check + (slots check - 1 : ℕ) * upward check) :
    (∑ check ∈ checks, fee check) ≤
      ((D - ∑ check ∈ occupied, slots check : ℕ) : ℝ) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check - 1 : ℕ) * upward check) := by
  classical
  rw [← Finset.sum_sdiff hsub]
  have hs : ∑ check ∈ checks \ occupied, slots check = D - ∑ check ∈ occupied, slots check := by
    have := Finset.sum_sdiff hsub (f := slots)
    omega
  refine add_le_add ?_ (Finset.sum_le_sum fun c hc => hhot c hc)
  rw [← hs, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun c hc => ?_
  rw [Finset.mem_sdiff] at hc
  exact hcold c hc.1 hc.2


