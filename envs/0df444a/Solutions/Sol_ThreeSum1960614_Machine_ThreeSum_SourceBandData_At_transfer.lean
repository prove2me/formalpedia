-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SourceBandData.At.transfer
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:07:27.055656+00:00
-- url     : https://prove2.me/submissions/d6acadad-9dc4-456a-ae2b-7f88ec33dce8

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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.SourceBandData
end ThreeSum.SourceBandData
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandData
end ThreeSum1960614.Machine.ThreeSum.SourceBandData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition




















theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    _root_.ThreeSum.LightHistogram.count key r (i + 1) = _root_.ThreeSum.LightHistogram.count key r i + if key i = r then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]













end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : _root_.ThreeSum.LightSourceResidues.key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm] at h
  exact_mod_cast h











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets
open _root_.ThreeSum.SourceBuckets


open _root_.Finset
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000





theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    _root_.ThreeSum.SourceBuckets.offset key N (r+1) = _root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightHistogram.count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (_root_.ThreeSum.SourceBuckets.offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (_root_.ThreeSum.LightHistogram.count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    _root_.ThreeSum.LightHistogram.count key r i < _root_.ThreeSum.LightHistogram.count key r j := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    _root_.ThreeSum.SourceBuckets.offset key N M = N := by
  unfold _root_.ThreeSum.SourceBuckets.offset _root_.ThreeSum.LightHistogram.count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBuckets.offset key N r ≤ N := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_mono key N hr).trans_eq (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_total hkey)





theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < _root_.ThreeSum.SourceBuckets.offset key N (key i+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  exact Nat.add_lt_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < N :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_end hi).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (by have hk := hkey i hi; omega))

























end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandLayout


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets












theorem len_le_cap (n g i : ℕ) : _root_.ThreeSum.SourceBandLayout.len n g i ≤ _root_.ThreeSum.SourceBandLayout.cap n g := by
  have hn := _root_.ThreeSum.BandPartition.stop_le n g i
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g i
  unfold _root_.ThreeSum.SourceBandLayout.len _root_.ThreeSum.SourceBandLayout.cap
  exact le_min (by omega) hg































theorem key_lt {f : ℕ → ℤ} {g p m : ℕ} {shift : ℤ} (hm : 0 < m) (i j : ℕ) :
    _root_.ThreeSum.SourceBandLayout.key f g p m shift i j < m := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_lt hm shift _

end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
section


theorem ThreeSum1960614.Machine.ThreeSum.SourceBandData.At.transfer__implementation_f9feb42b14 {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At μ f base n g p m shift i) (hm : 0 < m)
    (hhead : ∀ q < 6, ν (base+6*i+q)=μ (base+6*i+q))
    (hdata : ∀ x, _root_.ThreeSum.SourceBandLayout.hist base n g m i ≤ x → x < _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g → ν x=μ x) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At ν f base n g p m shift i := by
  have hcap := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap n g i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,⟨?_,?_⟩⟩
  · simpa only [Nat.add_zero] using (hhead 0 (by omega)).trans H.headStart
  · exact (hhead 1 (by omega)).trans H.headLength
  · exact (hhead 2 (by omega)).trans H.headCodes
  · exact (hhead 3 (by omega)).trans H.headHist
  · exact (hhead 4 (by omega)).trans H.headOffsets
  · exact (hhead 5 (by omega)).trans H.headFlat
  · intro j hj
    rw [hdata _ (by unfold _root_.ThreeSum.SourceBandLayout.codes; omega) (by unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes; omega)]
    exact H.codesRead j hj
  · intro r hr
    rw [hdata _ (by omega) (by unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes; omega)]
    exact H.histRead r hr
  · intro r hr
    rw [hdata _ (by unfold _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes; omega) (by unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor; omega)]
    exact H.buckets.offsets r hr
  · intro j hj
    have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_lt (fun q _ => _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hj
    rw [hdata _ (by unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes; omega) (by omega)]
    exact H.buckets.indices j hj
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SourceBandData.At.transfer__implementation_f9feb42b14) := (@ThreeSum1960614.Machine.ThreeSum.SourceBandData.At.transfer__implementation_f9feb42b14)

#print axioms solution
