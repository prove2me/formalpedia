-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.prefixRows_append
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:48:08.042+00:00
-- url     : https://prove2.me/submissions/45bcc53a-eab6-4e73-a9b0-9d7a9d3f6e98

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle11
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced



































































































































































































theorem prefixRows_append_sourceProof {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k < J) (S : Finset (Fin L)) :
    prefixRows (J := J) (pre ++ [S]) = Function.update (prefixRows pre) ⟨k,hk⟩ S := by
  funext i
  by_cases hi : i.val < k
  · have hne : i ≠ ⟨k,hk⟩ := by
      intro he
      have hv : i.val = k := congrArg Fin.val he
      omega
    rw [Function.update_of_ne hne]
    simp only [prefixRows]
    rw [List.getElem?_append_left (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega)]
  · by_cases he : i = ⟨k,hk⟩
    · subst i
      simp [prefixRows,hp]
    · have hv : k < i.val := by
        have hn : i.val ≠ k := fun h => he (Fin.ext h)
        omega
      rw [Function.update_of_ne he]
      simp only [prefixRows]
      rw [List.getElem?_append_right (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega),hp]
      rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]

























end ThreeSum.ReportingHostMasks

end


theorem solution : ∀ {J L k : Nat} (pre : List.{0} (Finset.{0} (Fin L))),
  @Eq.{1} Nat (@List.length.{0} (Finset.{0} (Fin L)) pre) k →
    ∀ (hk : @LT.lt.{0} Nat instLTNat k J) (S : Finset.{0} (Fin L)),
      @Eq.{1} (Fin J → Finset.{0} (Fin L))
        (@ThreeSum.StoredReporting.prefixRows J L
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Finset.{0} (Fin L))) (List.{0} (Finset.{0} (Fin L)))
            (List.{0} (Finset.{0} (Fin L)))
            (@instHAppendOfAppend.{0} (List.{0} (Finset.{0} (Fin L))) (@List.instAppend.{0} (Finset.{0} (Fin L)))) pre
            (@List.cons.{0} (Finset.{0} (Fin L)) S (@List.nil.{0} (Finset.{0} (Fin L))))))
        (@Function.update.{1, 1} (Fin J) (fun (a : Fin J) => Finset.{0} (Fin L)) (instDecidableEqFin J)
          (@ThreeSum.StoredReporting.prefixRows J L pre) (@Fin.mk J k hk) S) := by
  exact @ThreeSum.ReportingHostMasks.prefixRows_append_sourceProof

#print axioms solution
