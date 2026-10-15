-- Prove2me | solution 1 for ThreeSum.LightLocalCoverSchedule.indices_lt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:48:50.334648+00:00
-- url     : https://prove2.me/submissions/ec6aca7d-8658-4ec7-83e1-9bb5c96ea652

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

section


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]






theorem selectMap_mem (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    selectMap maps covers targets ∈ maps := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)








































































































































end ThreeSum.Cover

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators





















































theorem choice_lt {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ} (hrows : 0 < rows) (t : ℕ) :
    choice matrix rows cols t < rows := by
  apply List.mem_range.mp
  exact Cover.selectMap_mem _ (by simpa using hrows.ne') _ _





















































theorem choices_succ (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    choices matrix rows cols (t+1) = choices matrix rows cols t ++ [choice matrix rows cols t] := rfl

end ThreeSum.BooleanGreedy

end

section


/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding












theorem rows_pos (h : ℕ) : 0 < rows h := Nat.pow_pos (localPrime_pos h)

































































theorem indices_lt_sourceProof (h : ℕ) {i : ℕ} (hi : i ∈ indices h) : i < rows h := by
  have hchoices : ∀ t, ∀ j ∈ BooleanGreedy.choices (matrix h) (rows h) (cols h) t, j < rows h := by
    intro t
    induction t with
    | zero => intro j hj; simp [BooleanGreedy.choices,Cover.greedyChoices] at hj
    | succ t ih =>
      intro j hj
      rw [BooleanGreedy.choices_succ,List.mem_append,List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact ih j hj
      · exact BooleanGreedy.choice_lt (rows_pos h) t
  exact hchoices _ i hi


























































end ThreeSum.LightLocalCoverSchedule

end


theorem solution : ∀ (h : Nat) {i : Nat},
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) (ThreeSum.LightLocalCoverSchedule.indices h)
      i →
    @LT.lt.{0} Nat instLTNat i (ThreeSum.LightLocalCoverSchedule.rows h) := by
  exact @ThreeSum.LightLocalCoverSchedule.indices_lt_sourceProof

#print axioms solution
