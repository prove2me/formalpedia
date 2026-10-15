-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.tuples_nodup
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:51.061318+00:00
-- url     : https://prove2.me/submissions/332870cf-a7a7-4343-b49f-9ba4216f2495

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists

variable {α β : Type*}






























































theorem tuples_nodup_sourceProof (base : List α) (hbase : base.Nodup) (j : ℕ) :
    (tuples base j).Nodup := by
  induction j with
  | zero => simp [tuples]
  | succ j ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a ha
      exact ih.map (fun xs ys he => (List.cons.inj he).2)
    · exact hbase.imp (fun {a b} hab xs hxs hys => by
        obtain ⟨tail,_,rfl⟩ := List.mem_map.mp hxs
        obtain ⟨other,_,he⟩ := List.mem_map.mp hys
        exact hab (List.cons.inj he).1.symm)






































end ThreeSum.RadixKeyLists

end

universe u_1

theorem solution : ∀ {α : Type u_1} (base : List.{u_1} α),
  @List.Nodup.{u_1} α base →
    ∀ (j : Nat), @List.Nodup.{u_1} (List.{u_1} α) (@ThreeSum.RadixKeyLists.tuples.{u_1} α base j) := by
  exact @ThreeSum.RadixKeyLists.tuples_nodup_sourceProof

#print axioms solution
