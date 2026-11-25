-- Prove2me | solution 1 for SimpleGraph.goodman_bound_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:52.387799+00:00
-- url     : https://prove2.me/submissions/3e28c782-71d4-450e-be39-f65dfe460298

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
public import Theorems.Thm_SimpleGraph_goodman_sq_within
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
namespace SimpleGraph
theorem _root_.solution (S : Finset V) :
    #S * (#S - 1) * (#S - 5) ≤ 24 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) := by
  have h := goodman_sq_within G S
  have hnn : 0 ≤ ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hc := six_mul_choose_three (#S)
  rcases Nat.lt_or_ge (#S) 5 with h5 | h5
  · rw [show #S - 5 = 0 by omega, mul_zero]
    exact Nat.zero_le _
  zify [h5, show 1 ≤ #S by omega]
  push_cast at h
  linarith
end SimpleGraph
