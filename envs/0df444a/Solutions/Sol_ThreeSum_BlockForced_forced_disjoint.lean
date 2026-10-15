-- Prove2me | solution 1 for ThreeSum.BlockForced.forced_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:40:17.077332+00:00
-- url     : https://prove2.me/submissions/b70ccccf-990b-4b35-9034-bde3d8291545

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle10
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

section


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators











@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma






































































































end ThreeSum.BlockRows

end

section


/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

section FiniteRows

variable {J L : ℕ}










private theorem suffix_not_prefix {I : Finset (Fin J)} {Q : Fin J → Finset (Fin L)}
    {x : Finset (Coord J L)} (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I)
    (a : Fin L) : Sigma.mk i a ∉ x := by
  intro ha
  exact (Finset.mem_compl.mp (mem_join.mp (hx ha)).1) hi
































theorem forced_disjoint_sourceProof (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    Disjoint (prefixLeft I u ∪ x) (prefixRight I Q u ∪ (remaining I Q \ x)) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, a⟩ hL hR
  by_cases hi : i ∈ I
  · have hn := suffix_not_prefix hx hi a
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, hi, not_true_eq_false, true_and,
      false_and, or_false, false_or, hn] at hL hR
    exact hR.2 hL
  · simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, hi, not_false_eq_true, true_and,
      false_and, or_false, false_or] at hL hR
    exact hR.2 hL





































end FiniteRows



























































































section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]









































































end WeightedCounts

end ThreeSum.BlockForced

end


theorem solution : ∀ {J L : Nat} (I : Finset.{0} (Fin J)) (Q u : Fin J → Finset.{0} (Fin L))
  (x : Finset.{0} (ThreeSum.BlockRows.Coord J L)),
  @LE.le.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
      (@Preorder.toLE.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
          (@Finset.instPartialOrder.{0} (ThreeSum.BlockRows.Coord J L))))
      x (@ThreeSum.BlockForced.remaining J L I Q) →
    @Disjoint.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
      (@Finset.instPartialOrder.{0} (ThreeSum.BlockRows.Coord J L))
      (@Finset.instOrderBot.{0} (ThreeSum.BlockRows.Coord J L))
      (@Union.union.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
        (@Finset.instUnion.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
          @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
            (fun (a : Fin J) => instDecidableEqFin L) a b)
        (@ThreeSum.BlockForced.prefixLeft J L I u) x)
      (@Union.union.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
        (@Finset.instUnion.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
          @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
            (fun (a : Fin J) => instDecidableEqFin L) a b)
        (@ThreeSum.BlockForced.prefixRight J L I Q u)
        (@SDiff.sdiff.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
          (@Finset.instSDiff.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
            @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
              (fun (a : Fin J) => instDecidableEqFin L) a b)
          (@ThreeSum.BlockForced.remaining J L I Q) x)) := by
  exact @ThreeSum.BlockForced.forced_disjoint_sourceProof

#print axioms solution
