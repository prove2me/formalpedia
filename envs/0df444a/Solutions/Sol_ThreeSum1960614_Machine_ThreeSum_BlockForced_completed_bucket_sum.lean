-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:46.853467+00:00
-- url     : https://prove2.me/submissions/11501de0-7762-4bfe-ac22-6abebf775822

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.flat u ↔ x ∈ u i := by
  simp only [_root_.ThreeSum.BlockRows.flat, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_univ, true_and]



@[simp] theorem row_flat {J L : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum.BlockRows.flat u) i = u i := by ext x; simp

@[simp] theorem flat_row {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) : _root_.ThreeSum.BlockRows.flat (_root_.ThreeSum.BlockRows.row S) = S := by
  ext ⟨i, x⟩; simp



theorem row_subset {J L : ℕ} {S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)} (h : S ⊆ T) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row S i ⊆ _root_.ThreeSum.BlockRows.row T i := by
  intro x hx
  exact _root_.ThreeSum.BlockRows.mem_row.mpr (h (_root_.ThreeSum.BlockRows.mem_row.mp hx))



@[simp] theorem row_union {J L : ℕ} (S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (S ∪ T) i = _root_.ThreeSum.BlockRows.row S i ∪ _root_.ThreeSum.BlockRows.row T i := by ext x; simp





theorem join_union_compl {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.BlockRows.join I u ∪ _root_.ThreeSum.BlockRows.join Iᶜ u = _root_.ThreeSum.BlockRows.flat u := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_compl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat]
  tauto



















end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments






















theorem retained_survives {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c) := c.property





































































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows











@[simp] theorem row_leftSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) i = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1 := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _

@[simp] theorem row_rightSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) i = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.2 := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _

@[simp] theorem row_outputSubset {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (i : Fin J) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset q) i = (q i).2.val := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_flat _ _







theorem leftSubset_disjoint_right {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    Disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hL hR
  exact Finset.disjoint_left.mp (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).2.2
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat.mp hL) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat.mp hR)

theorem leftSubset_union_right {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ∪ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t) := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_flat,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice, _root_.ThreeSum.LocalGraph.output]

theorem rightSubset_eq_sdiff {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t) \ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_union_right]
  have hd := Finset.disjoint_left.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_disjoint_right t)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

/-- The occurrence and union tuple together with the left subset determine
both endpoints, including all schedule multiplicity tags. -/
theorem tuple_eq_of_output_leftSubset {h J : ℕ} {s t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J}
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput s = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t) (hL : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset s = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) : s = t := by
  have hR : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset s = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset_eq_sdiff, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset_eq_sdiff, hq, hL]
  funext i
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q => (q i).1) hq
  · apply Subtype.ext
    exact Prod.ext (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge] using congrArg (fun S => _root_.ThreeSum.BlockRows.row S i) hL)
      (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge] using congrArg (fun S => _root_.ThreeSum.BlockRows.row S i) hR)













section

private theorem private_a829934bec_positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : _root_.ThreeSum.Radix.positionalHash p g (xs.map f) =
      _root_.ThreeSum.Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, _root_.ThreeSum.Radix.positionalHash, ih]
end


theorem leftAllowed_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) := by
  intro i
  have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset] using (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).1, ?_⟩
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives (t i)).1
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum.LocalGraph.left, ho] using hs

theorem rightAllowed_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) := by
  intro i
  have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset] using (_root_.ThreeSum.LocalGraph.edge_data (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i))).2.1, ?_⟩
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives (t i)).2
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset, _root_.ThreeSum.LocalGraph.right, ho] using hs

theorem endpointLeft_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t := by
  have hl : (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i))
      (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) i))) = (List.ofFn t).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft, _root_.ThreeSum.LocalGraph.left, ho]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft, hl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.private_a829934bec_positionalHash_map]
  rfl

theorem endpointRight_choice {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t := by
  have hl : (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i))
      (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) i))) = (List.ofFn t).map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence (t i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_rightSubset, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight, _root_.ThreeSum.LocalGraph.right, ho]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight, hl, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.private_a829934bec_positionalHash_map]
  rfl



@[simp] theorem leftSubset_fromSubsets {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S V : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) (hS : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S)
    (hV : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o V) (hd : Disjoint S V) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.fromSubsets o S V hS hV hd) = S := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.flat_row S



theorem output_fromSubsets {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (S V : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) (hS : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) S)
    (hV : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) V) (hd : Disjoint S V)
    (hu : S ∪ V = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset q) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.fromSubsets (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) S V hS hV hd) = q := by
  funext i
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.fromSubsets, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_union, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_outputSubset, _root_.ThreeSum.LocalGraph.output] using congrArg (fun S => _root_.ThreeSum.BlockRows.row S i) hu

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]









theorem leftWeights_choice {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftAllowed_choice t q hq, ite_true, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft_choice t q hq,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket]

theorem rightWeights_choice {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t) = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightAllowed_choice t q hq, ite_true, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight_choice t q hq,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket]

end Histograms

end ThreeSum.BlockEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced
open _root_.ThreeSum.BlockForced


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding

section FiniteRows

variable {J L : ℕ}









section

private theorem private_9df4cd7b5e_suffix_not_prefix {I : Finset (Fin J)} {Q : Fin J → Finset (Fin L)}
    {x : Finset (_root_.ThreeSum.BlockRows.Coord J L)} (hx : x ⊆ _root_.ThreeSum.BlockForced.remaining I Q) {i : Fin J} (hi : i ∈ I)
    (a : Fin L) : Sigma.mk i a ∉ x := by
  intro ha
  exact (Finset.mem_compl.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp (hx ha)).1) hi
end






theorem row_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (hx : x ⊆ _root_.ThreeSum.BlockForced.remaining I Q) {i : Fin J} (hi : i ∈ I) :
    _root_.ThreeSum.BlockRows.row (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x) i = u i := by
  ext a
  simp only [_root_.ThreeSum.BlockRows.mem_row, Finset.mem_union, _root_.ThreeSum.BlockForced.prefixLeft, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, hi, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.private_9df4cd7b5e_suffix_not_prefix hx hi a, or_false]

theorem suffix_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (hx : x ⊆ _root_.ThreeSum.BlockForced.remaining I Q) :
    _root_.ThreeSum.BlockRows.join Iᶜ (_root_.ThreeSum.BlockRows.row (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x)) = x := by
  ext ⟨i, a⟩
  by_cases hi : i ∈ I
  · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_compl, hi, not_true_eq_false, false_and,
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.private_9df4cd7b5e_suffix_not_prefix hx hi a]
  · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_compl, hi, not_false_eq_true, true_and,
      _root_.ThreeSum.BlockRows.mem_row, Finset.mem_union, _root_.ThreeSum.BlockForced.prefixLeft, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, false_and, false_or]

theorem forced_left_of_agreement (I : Finset (Fin J)) (u v : Fin J → Finset (Fin L))
    (hv : ∀ i ∈ I, v i = u i) :
    _root_.ThreeSum.BlockForced.prefixLeft I u ∪ _root_.ThreeSum.BlockRows.join Iᶜ v = _root_.ThreeSum.BlockRows.flat v := by
  have he : _root_.ThreeSum.BlockRows.join I u = _root_.ThreeSum.BlockRows.join I v := by
    ext ⟨i, a⟩
    by_cases hi : i ∈ I
    · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, hi, true_and, hv i hi]
    · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, hi, false_and]
  rw [_root_.ThreeSum.BlockForced.prefixLeft, he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_union_compl I v

section

private theorem private_92cb238d05_sdiff_of_disjoint_union {S V Q : Finset (_root_.ThreeSum.BlockRows.Coord J L)}
    (hd : Disjoint S V) (hu : S ∪ V = Q) : V = Q \ S := by
  rw [← hu]
  have hd' := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop
end


end FiniteRows







theorem residual_subset {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t ⊆ _root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) := by
  have hL : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputSubset q := by
    rw [← hq, ← _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_union_right]
    exact Finset.subset_union_left
  intro ⟨i, a⟩ hx
  obtain ⟨hi, ha⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr
  refine ⟨hi, ?_⟩
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.row_subset hL i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_outputSubset] at hh
  exact hh ha

theorem forced_left_completion {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)
    (ht : t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) : _root_.ThreeSum.BlockForced.prefixLeft I u ∪ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_of_agreement I u _ (Finset.mem_filter.mp ht).2.2

theorem forced_right_completion {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h)))
    (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)
    (ht : t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) :
    _root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset t := by
  have hq := (Finset.mem_filter.mp ht).2.1
  have hx := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_subset q I t hq
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.private_92cb238d05_sdiff_of_disjoint_union (_root_.ThreeSum.BlockForced.forced_disjoint I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) hx)
    (_root_.ThreeSum.BlockForced.forced_union I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u hu (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t) hx)
  rw [he, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u t ht, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightSubset_eq_sdiff, hq]
  rfl



theorem residual_mem {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h)))
    (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)
    (ht : t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.admissibleResiduals q I u := by
  have hq := (Finset.mem_filter.mp ht).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_subset q I t hq), ?_⟩
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u t ht, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_right_completion q I u hu t ht]
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftAllowed_choice t q hq, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightAllowed_choice t q hq⟩

theorem residual_injective {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) :
    Set.InjOn (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual (h := h) I) (↑(_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u) : Set (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J)) := by
  intro s hs t ht he
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.tuple_eq_of_output_leftSubset
  · exact (Finset.mem_filter.mp hs).2.1.trans (Finset.mem_filter.mp ht).2.1.symm
  · rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u s hs, ← _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u t ht, he]

theorem residual_surjective {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i)
    (x : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) (hx : x ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.admissibleResiduals q I u) :
    ∃ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t = x := by
  obtain ⟨hx, hL, hR⟩ := Finset.mem_filter.mp hx
  have hxs := Finset.mem_powerset.mp hx
  let S := _root_.ThreeSum.BlockForced.prefixLeft I u ∪ x
  let V := _root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ x)
  have hd : Disjoint S V := _root_.ThreeSum.BlockForced.forced_disjoint I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u x hxs
  let t := _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.fromSubsets (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) S V hL hR hd
  have hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q := _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.output_fromSubsets q S V hL hR hd
    (_root_.ThreeSum.BlockForced.forced_union I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u hu x hxs)
  have hleft : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset t = S := _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftSubset_fromSubsets _ _ _ _ _ _
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, ?_⟩, ?_⟩
  · intro i hi
    have he := congrArg (fun S => _root_.ThreeSum.BlockRows.row S i) hleft
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset, S, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.row_forced_prefix I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u x hxs hi] using he
  · change _root_.ThreeSum.BlockRows.join Iᶜ (fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1) = x
    have he : (fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1) = _root_.ThreeSum.BlockRows.row S := by
      funext i
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.row_leftSubset] using congrArg (fun S => _root_.ThreeSum.BlockRows.row S i) hleft
    rw [he]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.suffix_forced_prefix I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u x hxs

section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]







end WeightedCounts

end ThreeSum.BlockForced

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum__implementation_22935bfa4c {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i) :
    (∑ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t * _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t) =
      ∑ x ∈ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)).powerset,
        _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x) *
        _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c
          (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ x)) := by
  calc
    _ = ∑ x ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.admissibleResiduals q I u,
        _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x) *
        _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c
          (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ x)) := by
      apply Finset.sum_bij (fun t _ => _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual I t)
      · exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_mem q I u hu
      · intro s hs t ht he
        exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_injective q I u hs ht he
      · intro x hx
        obtain ⟨t, ht, he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.residual_surjective q I u hu x hx
        exact ⟨t, ht, he⟩
      · intro t ht
        have hq := (Finset.mem_filter.mp ht).2.1
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_left_completion q I u t ht, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.forced_right_completion q I u hu t ht,
          _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights_choice P B b t q hq, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights_choice P d C c t q hq]
    _ = _ := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.admissibleResiduals, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hL : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x)
      · by_cases hR : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q)
            (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ x))
        · simp only [hL, hR, and_self, ite_true]
        · simp only [hL, hR, and_false, ite_false, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights, mul_zero]
      · simp only [hL, false_and, ite_false, _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights, zero_mul]
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum__implementation_22935bfa4c.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum__implementation_22935bfa4c.{u_implementation_0,u_implementation_1})

#print axioms solution
