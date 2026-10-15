-- Prove2me | solution 1 for ThreeSum.WantedRecordOrder.label_injective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:21:23.062087+00:00
-- url     : https://prove2.me/submissions/5d4205e2-44aa-4d68-8689-744ea291c5f6

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum_RadixKeyLists_tuples_nodup
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)




theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1

theorem maskAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : maskAt L h i = maskAt L h j) : i=j := by
  have hi' : i < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hi
  have hj' : j < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hj
  exact (List.getD_inj hi' hj' (enumerateLayer_nodup L h)).mp he

theorem setAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : setAt L h i = setAt L h j) : i=j := by
  apply maskAt_injective hi hj
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj,he]













































end ThreeSum.LocalMaskGraph

end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000






theorem layerRecord_injective (h : ℕ) : Function.Injective (layerRecord h) := by
  intro i j he
  apply Fin.ext
  exact LocalMaskGraph.setAt_injective i.isLt j.isLt (congrArg Subtype.val he)

















theorem layers_nodup (h : ℕ) : (layers h).Nodup :=
  List.nodup_ofFn_ofInjective (layerRecord_injective h)














theorem localRecords_nodup (h : ℕ) : (localRecords h).Nodup :=
  (List.nodup_finRange _).product (layers_nodup h)




























theorem globalRecords_nodup (h J : ℕ) : (globalRecords h J).Nodup := by
  apply ((tuples_nodup _ (localRecords_nodup h) J).attach).map
  intro xs ys he
  apply Subtype.ext
  have he' := congrArg List.ofFn he
  simpa only [ofFn_tupleOfList] using he'





















































end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# Original wanted labels behind the interleaved pair indices

Left indices recover the A-incidence position and its lift. Right indices
recover the unchanged global output record. The maps retain distinct source
positions even when their integer key values coincide.
-/

namespace ThreeSum.WantedRecordOrder

open GlobalEncoding GlobalKeyEnumeration RawIncidences RawAKeyLists
open OutputDecodeOrder

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000


















































theorem label_injective_sourceProof {xs : List ℤ} {h J i i' j j' : ℕ}
    (hi : i < 3*xs.length) (hi' : i' < 3*xs.length)
    (hj : j < LightGuardedWanted.totalKeys h J) (hj' : j' < LightGuardedWanted.totalKeys h J)
    (he : label h J i j hi=label h J i' j' hi') : i=i' ∧ j=j' := by
  have hr : i%xs.length=i'%xs.length := congrArg (fun w => w.1.val) he
  have hq : i/xs.length=i'/xs.length := congrArg (fun w => w.2.1.val) he
  have ho := congrArg (fun w => w.2.2) he
  have hj0 : j < (globalRecords h J).length := by
    rwa [OutputDecodeRecords.globalRecords_length']
  have hj1 : j' < (globalRecords h J).length := by
    rwa [OutputDecodeRecords.globalRecords_length']
  have hget : (globalRecords h J).get ⟨j,hj0⟩=(globalRecords h J).get ⟨j',hj1⟩ := by
    simpa only [label,LightOutputDecodeOriginal.output,List.getD_eq_getElem _ _ hj0,
      List.getD_eq_getElem _ _ hj1,List.get_eq_getElem] using ho
  have hh := congrArg Fin.val ((globalRecords_nodup h J).injective_get hget)
  refine ⟨?_,hh⟩
  have hi0 := Nat.div_add_mod i xs.length
  have hi1 := Nat.div_add_mod i' xs.length
  rw [hq,hr] at hi0
  omega































end ThreeSum.WantedRecordOrder

end


theorem solution : ∀ {xs : List.{0} Int} {h J i i' j j' : Nat}
  (hi :
    @LT.lt.{0} Nat instLTNat i
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs)))
  (hi' :
    @LT.lt.{0} Nat instLTNat i'
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))),
  @LT.lt.{0} Nat instLTNat j (ThreeSum.LightGuardedWanted.totalKeys h J) →
    @LT.lt.{0} Nat instLTNat j' (ThreeSum.LightGuardedWanted.totalKeys h J) →
      @Eq.{1} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs)))
          (@ThreeSum.WantedRecordOrder.label xs h J i j hi) (@ThreeSum.WantedRecordOrder.label xs h J i' j' hi') →
        And (@Eq.{1} Nat i i') (@Eq.{1} Nat j j') := by
  exact @ThreeSum.WantedRecordOrder.label_injective_sourceProof

#print axioms solution
