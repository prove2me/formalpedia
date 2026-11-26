-- Prove2me | solution 1 for Sendov.esymm_card_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:54:13.47706+00:00
-- url     : https://prove2.me/submissions/c459c462-23ca-479e-9057-5a981ae43d8e

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Maclaurin

set_option autoImplicit false
open Sendov
open Multiset
variable {a : ℝ} {t : Multiset ℝ}
namespace Sendov
theorem _root_.solution (a : ℝ) (t : Multiset ℝ) (ht : t ≠ 0) :
    (a ::ₘ t).esymm t.card = t.prod + a * t.esymm (t.card - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := ⟨t.card - 1, by
    have : 0 < t.card := Multiset.card_pos.2 ht
    omega⟩
  rw [hm]
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Nat.add_sub_cancel]
  congr 1
  · rw [← hm, Multiset.powersetCard_self]
    simp
  · rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro u _
    simp
end Sendov
