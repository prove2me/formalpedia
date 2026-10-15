-- Prove2me | solution 1 for ThreeSum.ReportingHostPairEnumeration.pairs_length
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:25.434208+00:00
-- url     : https://prove2.me/submissions/fa1ff1b5-60af-419b-86ee-46de5f9ec129

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
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
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset


























































































theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

















end ThreeSum.LayerCounts

end

section


/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration

open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph

set_option linter.unusedSimpArgs false












































































theorem pairs_length_sourceProof (L h : ℕ) :
    (pairs L h).length = L.choose (2*h)*(2*h).choose h := by
  have hm : ((lefts L h).map (fun S => ((rights S h).map (fun R => (S,R))).length)) =
      List.replicate (lefts L h).length ((L-h).choose h) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.length_map,List.getElem_replicate]
      exact rights_length _ ((lefts_mem _).mp (List.getElem_mem (by simpa using hi)))
  calc
    (pairs L h).length = (((lefts L h).map fun S => ((rights S h).map fun R => (S,R)).length)).sum := by
      simp [pairs,List.length_flatMap]
    _ = (lefts L h).length*((L-h).choose h) := by rw [hm]; simp
    _ = L.choose h*(L-h).choose h := by rw [lefts_length]
    _ = L.choose (2*h)*(2*h).choose h := LayerCounts.vertex_degree_identity L h










































end ThreeSum.ReportingHostPairEnumeration

end


theorem solution : ∀ (L h : Nat),
  @Eq.{1} Nat
    (@List.length.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      (ThreeSum.ReportingHostPairEnumeration.pairs L h))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (L.choose
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
      ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
        h)) := by
  exact @ThreeSum.ReportingHostPairEnumeration.pairs_length_sourceProof

#print axioms solution
