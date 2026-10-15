-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.localRecords_getD
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:58:26.978413+00:00
-- url     : https://prove2.me/submissions/fe906fe6-6666-49b8-be60-416c464cd992

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
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
















theorem localRecords_getD_sourceProof {h i : ℕ} (hi : i < localCount h) :
    (localRecords h).getD i (blockDefault h) =
      (⟨i/layerCount h,(Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr hi⟩,
        layerRecord h ⟨i%layerCount h,Nat.mod_lt _ (layerCount_pos h)⟩) := by
  have hq : i/layerCount h < scheduleSize h := (Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr hi
  have hr : i%layerCount h < layerCount h := Nat.mod_lt _ (layerCount_pos h)
  have hidx : i/layerCount h*layerCount h+i%layerCount h=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i (layerCount h)
  have hocc : (List.finRange (scheduleSize h)).getD (i/layerCount h) (blockDefault h).1 =
      ⟨i/layerCount h,hq⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_finRange] using hq)]
    apply Fin.ext
    simp
  have hmask : (layers h).getD (i%layerCount h) (blockDefault h).2 =
      layerRecord h ⟨i%layerCount h,hr⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [layers_length,layerCount] using hr)]
    simp only [layers,List.getElem_ofFn]
  unfold localRecords List.product
  conv_lhs => rw [← hidx]
  rw [getD_flatMap_uniform _ _ (layerCount h) (by simp [layers_length,layerCount])
    (blockDefault h).1 (blockDefault h) (by simpa only [List.length_finRange] using hq) hr]
  rw [hocc,List.getD_map_of_lt _ (by simpa only [layers_length,layerCount] using hr) (blockDefault h).2 (blockDefault h),hmask]









































































end ThreeSum.OutputDecodeRecords

end


theorem solution : ∀ {h i : Nat} (hi : @LT.lt.{0} Nat instLTNat i (ThreeSum.OutputDecodeRecords.localCount h)),
  @Eq.{1} (ThreeSum.GlobalEncoding.OutputBlock h)
    (@List.getD.{0} (ThreeSum.GlobalEncoding.OutputBlock h) (ThreeSum.GlobalKeyEnumeration.localRecords h) i
      (ThreeSum.OutputDecodeRecords.blockDefault h))
    (@Prod.mk.{0, 0} (ThreeSum.GlobalEncoding.Occurrence h)
      (↥(ThreeSum.LayerCounts.vertices
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))
      (@Fin.mk (ThreeSum.GlobalEncoding.scheduleSize h)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) i (ThreeSum.OutputDecodeRecords.layerCount h))
        (@Iff.mpr
          (@LT.lt.{0} Nat instLTNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) i
              (ThreeSum.OutputDecodeRecords.layerCount h))
            (ThreeSum.GlobalEncoding.scheduleSize h))
          (@LT.lt.{0} Nat instLTNat i
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.GlobalEncoding.scheduleSize h)
              (ThreeSum.OutputDecodeRecords.layerCount h)))
          (@Nat.div_lt_iff_lt_mul (ThreeSum.OutputDecodeRecords.layerCount h) i (ThreeSum.GlobalEncoding.scheduleSize h)
            (ThreeSum.OutputDecodeRecords.layerCount_pos h))
          hi))
      (ThreeSum.GlobalKeyEnumeration.layerRecord h
        (@Fin.mk
          ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h).choose
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (ThreeSum.OutputDecodeRecords.layerCount h))
          (@Nat.mod_lt i (ThreeSum.OutputDecodeRecords.layerCount h) (ThreeSum.OutputDecodeRecords.layerCount_pos h))))) := by
  exact @ThreeSum.OutputDecodeRecords.localRecords_getD_sourceProof

#print axioms solution
