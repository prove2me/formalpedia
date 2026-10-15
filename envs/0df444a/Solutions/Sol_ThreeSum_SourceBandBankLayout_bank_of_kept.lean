-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.bank_of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:54.754488+00:00
-- url     : https://prove2.me/submissions/5af8907a-38a7-41d1-8e07-12f8ff8001e8

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators









































































































































































































































theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [layerOffset_succ]
  omega






theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))

























































































































































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)







































end ThreeSum.SubsetAddress

end

section


/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout

open SubsetAddress LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : banks base count ≤ slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _









theorem right_end (base count W cut i : ℕ) :
    rightBase base count W cut i+family W cut = slot base count W cut (i+1) := by
  unfold rightBase leftBase flags rawRight rawLeft coeff1 coeff0 slot stride
  ring






theorem slot_le_masks {base count W cut i : ℕ} (hi : i ≤ count) :
    slot base count W cut i ≤ maskBase base count W cut := slot_mono base count W cut hi

theorem banks_le_work (base count W cut : ℕ) : banks base count ≤ work base count W cut := by
  have hm := banks_le_slot base count W cut count
  unfold work rowOut bitBase maskBase
  omega














theorem masks_le_work (base count W cut : ℕ) :
    maskBase base count W cut ≤ work base count W cut := by
  unfold work rowOut bitBase
  omega













theorem stage_cell_lt_end {W cut base j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase base (downsetCap W cut) j+subsetRank S < base+family W cut := by
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  calc
    _ < base+j*downsetCap W cut+downsetCap W cut := Nat.add_lt_add_left hr _
    _ = base+(j+1)*downsetCap W cut := by ring
    _ ≤ base+(W+1)*downsetCap W cut := Nat.add_le_add_left hm _
    _ = _ := rfl

theorem left_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (leftBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  have hs := stage_cell_lt_end (base := leftBase base count W cut i) hj hS
  have he := right_end base count W cut i
  unfold rightBase at he
  omega

theorem right_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase (rightBase base count W cut i) (downsetCap W cut) j+subsetRank S <
      slot base count W cut (i+1) := by
  rw [← right_end]
  exact stage_cell_lt_end hj hS


























end ThreeSum.LightBlockSourceBatchLayout

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder











































theorem bank_of_kept_sourceProof {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i bound : ℕ} {μ ν : ℕ → ℤ} {p shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : LightBlockSourceBatch.BankAt μ base count cut i p shift B b A a q)
    (hi : i < count) (K : Kept μ ν bound) (hb : work base count (J*(512*h)) cut ≤ bound) :
    LightBlockSourceBatch.BankAt ν base count cut i p shift B b A a q := by
  have hmask := masks_le_work base count (J*(512*h)) cut
  have hnext := slot_le_masks (base := base) (W := J*(512*h)) (cut := cut)
    (show i+1 ≤ count by omega)
  have hhead := banks_le_work base count (J*(512*h)) cut
  unfold banks at hhead
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hs := left_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.left j hj S hS)
  · intro j hj S hS
    have hs := right_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.right j hj S hS)
  · exact (K _ (by omega)).trans H.headerLeft
  · exact (K _ (by omega)).trans H.headerRight























end ThreeSum.SourceBandBankLayout

end

universe u_1 u_2

theorem solution : ∀ {β : Type u_1} {γ : Type u_2} [inst : Fintype.{u_1} β] [inst_1 : Fintype.{u_2} γ] [inst_2 : DecidableEq.{u_1 + 1} β]
  [inst_3 : DecidableEq.{u_2 + 1} γ] {h J base count cut i bound : Nat} {μ ν : Nat → Int} {p shift : Int}
  {B : Finset.{u_1} β} {b : β → Int} {A : Finset.{u_2} γ} {a : γ → Int} {q : ThreeSum.GlobalEncoding.GlobalOutput h J},
  @ThreeSum.LightBlockSourceBatch.BankAt.{u_1, u_2} β γ inst inst_1 inst_2 inst_3 h J μ base count cut i p shift B b A a
      q →
    @LT.lt.{0} Nat instLTNat i count →
      Light.Kept μ ν bound →
        @LE.le.{0} Nat instLENat
            (ThreeSum.LightBlockSourceBatchLayout.work base count
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              cut)
            bound →
          @ThreeSum.LightBlockSourceBatch.BankAt.{u_1, u_2} β γ inst inst_1 inst_2 inst_3 h J ν base count cut i p shift
            B b A a q := by
  exact @ThreeSum.SourceBandBankLayout.bank_of_kept_sourceProof

#print axioms solution
