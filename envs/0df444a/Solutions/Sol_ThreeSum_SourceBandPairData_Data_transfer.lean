-- Prove2me | solution 1 for ThreeSum.SourceBandPairData.Data.transfer
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:33.047671+00:00
-- url     : https://prove2.me/submissions/1caa3831-e604-48f0-8894-e090b778a602

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
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
import Theorems.Thm_ThreeSum_SourceBandData_At_transfer


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

section


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets













































theorem data_le_hist (base n g m i : ℕ) : data base n g ≤ hist base n g m i :=
  Nat.le_add_right _ _




































































end ThreeSum.SourceBandLayout

end

section


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩














theorem Data.transfer_sourceProof {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : ∀ a, leftBase base ≤ a → ν a=μ a) : Data ν fL fR base NL NR g p m shift := by
  have ho := ordered base NL NR g m
  refine ⟨?_,?_,?_⟩
  · intro i hi
    apply (H.left i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (leftBase base) NL g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro i hi
    apply (H.right i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (rightBase base NL g m) NR g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro r hr
    exact (K _ (by omega)).trans (H.zero r hr)





































end ThreeSum.SourceBandPairData

end


theorem solution : ∀ {μ ν fL fR : Nat → Int} {base NL NR g p m : Nat} {shift : Int},
  ThreeSum.SourceBandPairData.Data μ fL fR base NL NR g p m shift →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
      (∀ (a : Nat), @LE.le.{0} Nat instLENat (ThreeSum.SourceBandPairData.leftBase base) a → @Eq.{1} Int (ν a) (μ a)) →
        ThreeSum.SourceBandPairData.Data ν fL fR base NL NR g p m shift := by
  exact @ThreeSum.SourceBandPairData.Data.transfer_sourceProof

#print axioms solution
