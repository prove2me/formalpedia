-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.global_record_block
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:48.155751+00:00
-- url     : https://prove2.me/submissions/93dc899b-0034-4796-96b7-207526164b97

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_ThreeSum_OutputDecodeOrder_tuples_getD_indices


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists

section


/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000









theorem localCount_pos (h : ℕ) : 0 < localCount h := Nat.mul_pos (schedule_pos h) (layerCount_pos h)











































theorem globalRecords_map_ofFn (h J : ℕ) :
    (globalRecords h J).map List.ofFn = tuples (localRecords h) J := by
  simp [globalRecords,List.map_map,Function.comp_def,ofFn_tupleOfList]





theorem globalRecords_getD_ofFn {h J k : ℕ} (hk : k < localCount h^J) :
    List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (tuples (localRecords h) J).getD k [] := by
  have hi : k < (globalRecords h J).length := by rwa [globalRecords_length']
  have he := List.getD_map_of_lt (fun q : GlobalOutput h J => List.ofFn q) hi (outputDefault h J) []
  rw [globalRecords_map_ofFn] at he
  exact he.symm

theorem global_record_block_sourceProof {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    ((globalRecords h J).getD k (outputDefault h J)) j =
      (localRecords h).getD (localIndex h J k j.val) (blockDefault h) := by
  have hs : List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (indices (localCount h) J k).map (fun i => (localRecords h).getD i (blockDefault h)) := by
    rw [globalRecords_getD_ofFn hk]
    have he := tuples_getD_indices (localRecords h) (blockDefault h)
      (by simpa only [localRecords_length,localCount,layerCount] using localCount_pos h) J k
      (by simpa only [localRecords_length,localCount,layerCount] using hk)
    simpa only [localRecords_length,localCount,layerCount] using he
  have hc := congrArg (fun xs : List (OutputBlock h) => xs.getD j.val (blockDefault h)) hs
  have hleft : (List.ofFn ((globalRecords h J).getD k (outputDefault h J))).getD j.val (blockDefault h) =
      ((globalRecords h J).getD k (outputDefault h J)) j := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.getElem_ofFn]
  rw [hleft,List.getD_map_of_lt _ (by rw [indices_length]; exact j.isLt) 0 (blockDefault h)] at hc
  exact hc

























end ThreeSum.OutputDecodeRecords

end


theorem solution : ∀ {h J k : Nat},
  @LT.lt.{0} Nat instLTNat k
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount h) J) →
    ∀ (j : Fin J),
      @Eq.{1} (ThreeSum.GlobalEncoding.OutputBlock h)
        (@List.getD.{0} (ThreeSum.GlobalEncoding.GlobalOutput h J) (ThreeSum.GlobalKeyEnumeration.globalRecords h J) k
          (ThreeSum.OutputDecodeRecords.outputDefault h J) j)
        (@List.getD.{0} (ThreeSum.GlobalEncoding.OutputBlock h) (ThreeSum.GlobalKeyEnumeration.localRecords h)
          (ThreeSum.OutputDecodeRecords.localIndex h J k (@Fin.val J j)) (ThreeSum.OutputDecodeRecords.blockDefault h)) := by
  exact @ThreeSum.OutputDecodeRecords.global_record_block_sourceProof

#print axioms solution
