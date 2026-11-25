-- Prove2me | solution 1 for SimpleGraph.IsRegularOfDegree.goodman_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:56:31.044987+00:00
-- url     : https://prove2.me/submissions/d35817e7-8a4b-4b91-8df3-004ce966e900

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
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degree_add_degree_compl
public import Theorems.Thm_SimpleGraph_goodman_sq
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V] in
/-- `6 C(n, 3) = n (n - 1) (n - 2)`, over `ℤ`. -/
private theorem six_mul_choose_three (n : ℕ) :
    (6 * n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  rcases n with _ | _ | _ | n
  · simp [Nat.choose]
  · simp [Nat.choose]
  · simp [Nat.choose]
  · have : 6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
      rw [show 6 = Nat.factorial 3 from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
      simp only [show n + 3 - 2 = n + 1 by omega, show n + 3 - 1 = n + 2 by omega,
        Nat.sub_zero]
      ring
    have := congrArg (fun m : ℕ => (m : ℤ)) this
    push_cast at this ⊢
    linarith
section Fintype
variable [Fintype V]
end Fintype
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype V]
namespace SimpleGraph
namespace IsRegularOfDegree
theorem _root_.solution {k : ℕ} (hG : G.IsRegularOfDegree k)
    (hn : Fintype.card V = 2 * k + 1) :
    (24 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) : ℤ) =
      Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 5) := by
  have h := goodman_sq G
  have hd : ∀ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 = 0 := fun v => by
    have := degree_add_degree_compl G v
    rw [hG v, hn] at this
    rw [hG v, show Gᶜ.degree v = k by omega, sub_self]
    ring
  simp only [hd, sum_const_zero, add_zero] at h
  have hc := six_mul_choose_three (Fintype.card V)
  push_cast at h
  linarith
end IsRegularOfDegree
end SimpleGraph
