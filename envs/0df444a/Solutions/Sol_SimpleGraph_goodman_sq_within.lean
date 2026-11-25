-- Prove2me | solution 1 for SimpleGraph.goodman_sq_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:48:19.984847+00:00
-- url     : https://prove2.me/submissions/a1ff9593-3dad-418a-b4c4-6d20516a7bc3

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_degreeWithin_add_degreeWithin_compl
public import Theorems.Thm_SimpleGraph_goodman_within

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) :
    8 * ((G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3 : ℕ) : ℤ) + #S * ((#S : ℤ) - 1) ^ 2 =
      8 * (#S).choose 3 + ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := by
  have h := congrArg (fun m : ℕ => (m : ℤ)) (goodman_within G S)
  push_cast at h
  have hsq : ∀ v ∈ S, ((#S : ℤ) - 1) ^ 2 = 4 * (G.degreeWithin S v * Gᶜ.degreeWithin S v : ℤ) +
      ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := fun v hv => by
    have h1 := degreeWithin_add_degreeWithin_compl G hv
    have : (#S : ℤ) - 1 = G.degreeWithin S v + Gᶜ.degreeWithin S v := by omega
    rw [this]
    ring
  have hn : (#S : ℤ) * ((#S : ℤ) - 1) ^ 2 =
      4 * ∑ v ∈ S, (G.degreeWithin S v * Gᶜ.degreeWithin S v : ℤ) +
        ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_congr rfl hsq, sum_const, nsmul_eq_mul]
  rw [hn]
  push_cast
  linarith
end SimpleGraph
