-- Prove2me | solution 1 for SimpleGraph.goodman_bound_of_even_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:56:28.350173+00:00
-- url     : https://prove2.me/submissions/b52e95f6-81f2-43b9-a6ca-a13dc683b263

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
theorem _root_.solution (hn : Even (Fintype.card V)) :
    (Fintype.card V : ℤ) * (Fintype.card V - 2) * (Fintype.card V - 4) ≤
      24 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) := by
  have h := goodman_sq G
  have hone : ∀ v, 1 ≤ ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := fun v => by
    have hd := degree_add_degree_compl G v
    have hpos := Fintype.card_pos_iff.mpr ⟨v⟩
    obtain ⟨k, hk⟩ := hn
    have hz : (G.degree v : ℤ) - Gᶜ.degree v ≠ 0 := by
      intro h0
      have : G.degree v = Gᶜ.degree v := by omega
      omega
    have : 0 < ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by positivity
    exact Int.add_one_le_iff.mpr this
  have hsum : (Fintype.card V : ℤ) ≤ ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
    simpa using sum_le_sum fun v (_ : v ∈ univ) => hone v
  have hc := six_mul_choose_three (Fintype.card V)
  linarith
end SimpleGraph
