-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data.gathered_schedule
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:48:12.031222+00:00
-- url     : https://prove2.me/submissions/b2eb272b-11c4-44db-8369-b864fb0a2e16

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
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
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_map

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightWeightDecode
end ThreeSum.LightWeightDecode
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WeightEnumeration
end ThreeSum.WeightEnumeration
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
end ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
end ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WeightEnumeration
end ThreeSum1960614.Machine.ThreeSum.WeightEnumeration

namespace ThreeSum1960614.Machine

/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy
open _root_.ThreeSum.BooleanGreedy


open _root_.Finset
open scoped _root_.BigOperators



























theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (_root_.ThreeSum.BooleanGreedy.choices matrix rows cols t).length = t := _root_.ThreeSum.Cover.greedyChoices_length ..



end ThreeSum.BooleanGreedy

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]









end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration
open _root_.ThreeSum.WeightEnumeration


open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]





































theorem decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (_root_.ThreeSum.WeightEnumeration.decodedWeight (K := ZMod p) L p k i).val = _root_.ThreeSum.WeightEnumeration.digit p (2*L) k (_root_.ThreeSum.WeightEnumeration.coordinateIndex i) := by
  simp [_root_.ThreeSum.WeightEnumeration.decodedWeight,_root_.ThreeSum.WeightEnumeration.digit,ZMod.val_natCast]









end ThreeSum.WeightEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds













@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (i : Fin (464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s.val i.val = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s (i,b)).val := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,s.isLt,dite_true,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin]











end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum.LightLocalCoverSchedule


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding




















theorem indices_length (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_length ..





theorem candidateAt_lt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := by
  have hs : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact s.isLt
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_lt h (List.getElem_mem hs)

theorem candidateAt_mapAt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s := by
  have hs : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact s.isLt
  have hs' : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).length := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]
    exact s.isLt
  have he := congrArg (fun xs : List (_root_.ThreeSum.LocalHashMoments.Weight (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) => xs.getD s.val default) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_map h)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hs),List.getElem_map,
    List.getD_eq_getElem _ _ hs'] at he
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt
  rw [List.getD_eq_getElem _ _ hs]
  exact he







end ThreeSum.LightLocalCoverSchedule

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode
open _root_.ThreeSum.LightWeightDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem Rows.decodedWeight {μ : ℕ → ℤ} {dst L p k : ℕ}
    (hrows : _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.Rows μ dst L p k) (i : Fin L) :
    μ (dst+i.val) = ((_root_.ThreeSum.WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,false)).val : ℤ) ∧
    μ (dst+L+i.val) = ((_root_.ThreeSum.WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,true)).val : ℤ) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.decodedWeight_val,_root_.ThreeSum.WeightEnumeration.coordinateIndex,
    Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using hrows i.val i.isLt



end ThreeSum.LightWeightDecode

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
section


theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data.gathered_schedule__implementation_291a4350d3 {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr dst : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ h maps hist0 hist1 matrixPtr)
    (hcopy : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ a < 2*(464*h),
      ν (dst+s*(2*(464*h))+a) = μ (maps+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).getD s 0*(2*(464*h))+a)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows ν h dst := by
  intro s hs i hi
  let o : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h := ⟨s,hs⟩
  have hc := ((H (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h o) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_lt h o)).1).decodedWeight ⟨i,hi⟩
  change
    μ (maps+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h o*(2*(464*h))+i) = ((_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h o) (⟨i,hi⟩,false)).val : ℤ) ∧
    μ (maps+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h o*(2*(464*h))+464*h+i) = ((_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h o) (⟨i,hi⟩,true)).val : ℤ) at hc
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_mapAt h o] at hc
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin false o ⟨i,hi⟩,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin true o ⟨i,hi⟩]
  constructor
  · rw [hcopy s hs i (by omega)]
    exact hc.1
  · have he := hcopy s hs (464*h+i) (by omega)
    rw [← Nat.add_assoc,← Nat.add_assoc] at he
    rw [he]
    exact hc.2
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data.gathered_schedule__implementation_291a4350d3) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data.gathered_schedule__implementation_291a4350d3)

#print axioms solution
