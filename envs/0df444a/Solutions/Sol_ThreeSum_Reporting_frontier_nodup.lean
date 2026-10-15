-- Prove2me | solution 1 for ThreeSum.Reporting.frontier_nodup
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:39.33478+00:00
-- url     : https://prove2.me/submissions/1466e2ea-3e4d-4192-b33f-75e96aacede5

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]





















































































theorem frontier_nodup_sourceProof (children : ℕ → List α) (query : ℕ → List α → ℕ)
    (hc : ∀ k, (children k).Nodup) (k : ℕ) : (frontier children query k).Nodup := by
  induction k with
  | zero => unfold frontier; split <;> simp
  | succ k ih =>
      apply List.Nodup.filter
      apply List.nodup_flatMap.mpr
      constructor
      · intro pre hpre
        apply (hc k).map
        intro x y hxy
        exact List.singleton_injective (List.append_cancel_left hxy)
      · apply ih.imp
        intro p q hpq
        apply List.disjoint_left.mpr
        intro t ht hq
        obtain ⟨x, hx, hxt⟩ := List.mem_map.mp ht
        obtain ⟨y, hy, hyt⟩ := List.mem_map.mp hq
        have heq : p ++ [x] = q ++ [y] := hxt.trans hyt.symm
        exact hpq (List.append_inj_left' heq (by rfl))






































end ThreeSum.Reporting

end

universe u_2

theorem solution : ∀ {α : Type u_2} [DecidableEq.{u_2 + 1} α] (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat),
  (∀ (k : Nat), @List.Nodup.{u_2} α (children k)) →
    ∀ (k : Nat), @List.Nodup.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k) := by
  exact @ThreeSum.Reporting.frontier_nodup_sourceProof

#print axioms solution
