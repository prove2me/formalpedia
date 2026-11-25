-- Prove2me | solution 1 for SimpleGraph.supersaturation_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:44.041802+00:00
-- url     : https://prove2.me/submissions/1da1202b-e82b-4d50-9020-511fd272f589

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_supersaturation

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {t : ℕ} (ht : 2 ≤ t) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (t + t - 3)) :
    supersaturationBound t t ((#S : ℝ) + 1 - 2 ^ (t + t - 3)) ≤
      G.cliqueCountIn S t + Gᶜ.cliqueCountIn S t := by
  rcases supersaturation G (by omega) (by omega) (by omega) S hx with h | h
  · have := Nat.cast_nonneg (α := ℝ) (Gᶜ.cliqueCountIn S t); linarith
  · have := Nat.cast_nonneg (α := ℝ) (G.cliqueCountIn S t); linarith
end SimpleGraph
