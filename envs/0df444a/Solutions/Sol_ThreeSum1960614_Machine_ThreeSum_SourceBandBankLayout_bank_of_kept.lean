-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.bank_of_kept
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:41:39.132286+00:00
-- url     : https://prove2.me/submissions/30a0643e-c7d5-4750-8521-919a03739c40

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega





theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) :
    _root_.ThreeSum.SubsetAddress.downsetRank L m < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hmask : _root_.ThreeSum.SubsetAddress.IsMask L (_root_.ThreeSum.SubsetAddress.weight L m) m := ⟨hm, rfl⟩
  have hr := _root_.ThreeSum.SubsetAddress.layerRank_lt hmask
  unfold _root_.ThreeSum.SubsetAddress.downsetRank _root_.ThreeSum.SubsetAddress.downsetCap
  calc
    _ < _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m) + L.choose (_root_.ThreeSum.SubsetAddress.weight L m) := Nat.add_lt_add_left hr _
    _ = _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m + 1) := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L _).symm
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))





















































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    _root_.ThreeSum.SubsetAddress.subsetRank s < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask s
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.downsetRank_lt hm.1 (hm.2.trans_le hs)











end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum.LightBlockSourceBatchLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _





theorem right_end (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut = _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.stride
  ring



theorem slot_le_masks {base count W cut i : ℕ} (hi : i ≤ count) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_mono base count W cut hi

theorem banks_le_work (base count W cut : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut count
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase
  omega





theorem masks_le_work (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase
  omega



theorem stage_cell_lt_end {W cut base j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S < base+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  calc
    _ < base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.downsetCap W cut := Nat.add_lt_add_left hr _
    _ = base+(j+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut := by ring
    _ ≤ base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut := Nat.add_le_add_left hm _
    _ = _ := rfl

theorem left_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.stage_cell_lt_end (base := _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) hj hS
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end base count W cut i
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase at he
  omega

theorem right_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.stage_cell_lt_end hj hS









end ThreeSum.LightBlockSourceBatchLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
section

theorem ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.bank_of_kept__implementation_c304022335 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i bound : ℕ} {μ ν : ℕ → ℤ} {p shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base count cut i p shift B b A a q)
    (hi : i < count) (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound) (hb : _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt ν base count cut i p shift B b A a q := by
  have hmask := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.masks_le_work base count (J*(464*h)) cut
  have hnext := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_le_masks (base := base) (W := J*(464*h)) (cut := cut)
    (show i+1 ≤ count by omega)
  have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_work base count (J*(464*h)) cut
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hhead
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.left j hj S hS)
  · intro j hj S hS
    have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.right j hj S hS)
  · exact (K _ (by omega)).trans H.headerLeft
  · exact (K _ (by omega)).trans H.headerRight
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.bank_of_kept__implementation_c304022335.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.bank_of_kept__implementation_c304022335.{u_implementation_0,u_implementation_1})

#print axioms solution
