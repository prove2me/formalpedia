-- Prove2me | solution 1 for ThreeSum.DenseGuardWanted.pair_indices_injective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:07.727989+00:00
-- url     : https://prove2.me/submissions/bbe8bcad-bfe5-4899-a317-95a8b7f85013

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
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
namespace Light
end Light
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder

section


/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder







theorem pair_indices_injective_sourceProof {μ : ℕ → ℤ} {free NL NR M k k' : ℕ}
    {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ free M left right NL NR shift)
    (hk : k < (μ free).toNat) (hk' : k' < (μ free).toNat)
    (hl : leftIndex μ free NL NR M k=leftIndex μ free NL NR M k')
    (hr : rightIndex μ free NL NR M k=rightIndex μ free NL NR M k') : k=k' := by
  rcases H with ⟨hcount,_,_,_,ps,hlen,hn,_,hseg⟩
  have hk0 : k < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk
  have hk1 : k' < ps.length := by rw [hlen]; simpa only [hcount,Int.toNat_natCast] using hk'
  have hv (i : ℕ) (hi : i < ps.length) :
      (leftIndex μ free NL NR M i,rightIndex μ free NL NR M i)=ps.get ⟨i,hi⟩ := by
    obtain ⟨hL,hR⟩ := segment_pair hseg hi
    simp only [leftIndex,rightIndex,hL,hR,Int.toNat_natCast,
      List.getD_eq_getElem _ _ hi,List.get_eq_getElem]
  have hp : ps.get ⟨k,hk0⟩=ps.get ⟨k',hk1⟩ :=
    (hv k hk0).symm.trans ((Prod.ext hl hr).trans (hv k' hk1))
  exact congrArg Fin.val (hn.injective_get hp)





































































end ThreeSum.DenseGuardWanted

end


theorem solution : ∀ {μ : Nat → Int} {free NL NR M k k' : Nat} {left right : Nat → Int} {shift : Int},
  ThreeSum.LightWantedSetup.Output μ free M left right NL NR shift →
    @LT.lt.{0} Nat instLTNat k (μ free).toNat →
      @LT.lt.{0} Nat instLTNat k' (μ free).toNat →
        @Eq.{1} Nat (ThreeSum.DenseGuardWanted.leftIndex μ free NL NR M k)
            (ThreeSum.DenseGuardWanted.leftIndex μ free NL NR M k') →
          @Eq.{1} Nat (ThreeSum.DenseGuardWanted.rightIndex μ free NL NR M k)
              (ThreeSum.DenseGuardWanted.rightIndex μ free NL NR M k') →
            @Eq.{1} Nat k k' := by
  exact @ThreeSum.DenseGuardWanted.pair_indices_injective_sourceProof

#print axioms solution
