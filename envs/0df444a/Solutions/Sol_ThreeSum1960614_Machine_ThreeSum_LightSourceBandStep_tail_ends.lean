-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tail_ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:20.511988+00:00
-- url     : https://prove2.me/submissions/1817d5c9-fb81-4c83-b6a9-0a37922eb1f9

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketOriginal_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBandStep
end ThreeSum.LightSourceBandStep
namespace ThreeSum.LightSourceBucketFromHistogram
end ThreeSum.LightSourceBucketFromHistogram
namespace ThreeSum.LightSourceBucketOriginal
end ThreeSum.LightSourceBucketOriginal
namespace ThreeSum.LightSourceHistogram
end ThreeSum.LightSourceHistogram
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram
end ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
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
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}



/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Retained code/count arrays to exact contiguous original-index buckets

This actual three-procedure program is generic in the residue code function.
It constructs prefix offsets and scatters every physical index exactly once.
The code and count arrays are retained for source stages and later joins.
-/

namespace ThreeSum.LightSourceBucketFromHistogram
open _root_.ThreeSum.LightSourceBucketFromHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (N M : ℕ) : _root_.ThreeSum.LightSourceBucketFromHistogram.time N M ≤ 220*(N+M+1) := by
  unfold _root_.ThreeSum.LightSourceBucketFromHistogram.time _root_.ThreeSum.LightSourceBucketOffsets.time _root_.ThreeSum.LightSourceBucketScatter.time
  omega

end ThreeSum.LightSourceBucketFromHistogram

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

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (n p U D : ℕ) :
    _root_.ThreeSum.LightSourceResidues.time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by
  unfold _root_.ThreeSum.LightSourceResidues.time _root_.ThreeSum.LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact source histogram from original signed inputs

This complete wrapper computes the two-modulus key of every original input,
clears the histogram, and increments it once per input incidence. The carry
offset is supplied as a signed integer. No residue-array or histogram oracle
appears in the input contract.
-/

namespace ThreeSum.LightSourceHistogram
open _root_.ThreeSum.LightSourceHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (n p m U D : ℕ) :
    _root_.ThreeSum.LightSourceHistogram.time n p m U D ≤
      278*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+13*m+63 := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.time_bound n p U D
  unfold _root_.ThreeSum.LightSourceHistogram.time _root_.ThreeSum.LightHistogram.histogramTime _root_.ThreeSum.LightHistogram.countTime _root_.Light.fillTime
  nlinarith

end ThreeSum.LightSourceHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original signed inputs to retained histograms and exact index buckets

The actual code/histogram constructor runs once, followed by linear prefix
and scatter passes. Both source transforms and terminal Cartesian reporting
reuse these same counts and original-index fibers.
-/

namespace ThreeSum.LightSourceBucketOriginal
open _root_.ThreeSum.LightSourceBucketOriginal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (N p m U D : ℕ) :
    _root_.ThreeSum.LightSourceBucketOriginal.time N p m U D ≤ 498*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.time_bound N p m U D
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketFromHistogram.time_bound N m
  unfold _root_.ThreeSum.LightSourceBucketOriginal.time
  nlinarith

end ThreeSum.LightSourceBucketOriginal

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

theorem input_index {n g i j : ℕ} (hg : 0 < g) (hi : i < _root_.ThreeSum.BandPartition.size n g) (hj : j < _root_.ThreeSum.SourceBandLayout.len n g i) :
    _root_.ThreeSum.BandPartition.start g i+j < n := by
  have hlo := _root_.ThreeSum.BandPartition.start_lt_stop hg hi
  have hhi := _root_.ThreeSum.BandPartition.stop_le n g i
  unfold _root_.ThreeSum.SourceBandLayout.len at hj
  omega

theorem start_add_len {n g i : ℕ} (hg : 0 < g) (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    _root_.ThreeSum.BandPartition.start g i+_root_.ThreeSum.SourceBandLayout.len n g i = _root_.ThreeSum.BandPartition.stop n g i := by
  have hs := _root_.ThreeSum.BandPartition.start_lt_stop hg hi
  unfold _root_.ThreeSum.SourceBandLayout.len
  omega



theorem hist_mono (base n g m : ℕ) : Monotone (_root_.ThreeSum.SourceBandLayout.hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem data_le_hist (base n g m i : ℕ) : _root_.ThreeSum.SourceBandLayout.data base n g ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m i :=
  Nat.le_add_right _ _

theorem flat_end (base n g m i : ℕ) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g = _root_.ThreeSum.SourceBandLayout.hist base n g m (i+1) := by
  unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.stride
  ring

theorem header_end {base n g m i : ℕ} (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    base+6*i+6 ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m i := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m i
  unfold _root_.ThreeSum.SourceBandLayout.data at hb
  omega

theorem flat_end_le_work {base n g m i : ℕ} (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.hist_mono base n g m (by omega)





theorem count_congr {key key' : ℕ → ℕ} {N t : ℕ}
    (he : ∀ i < N, key i=key' i) (ht : t ≤ N) (r : ℕ) :
    _root_.ThreeSum.LightHistogram.count key r t=_root_.ThreeSum.LightHistogram.count key' r t := by
  unfold _root_.ThreeSum.LightHistogram.count
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le ht)]

theorem offset_congr {key key' : ℕ → ℕ} {N : ℕ}
    (he : ∀ i < N, key i=key' i) (r : ℕ) :
    _root_.ThreeSum.SourceBuckets.offset key N r=_root_.ThreeSum.SourceBuckets.offset key' N r := by
  unfold _root_.ThreeSum.SourceBuckets.offset
  apply Finset.sum_congr rfl
  intro s _
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.count_congr he le_rfl s

theorem position_congr {key key' : ℕ → ℕ} {N i : ℕ}
    (he : ∀ j < N, key j=key' j) (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i=_root_.ThreeSum.SourceBuckets.position key' N i := by
  unfold _root_.ThreeSum.SourceBuckets.position
  rw [he i hi,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.offset_congr he,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.count_congr he hi.le]

theorem buckets_congr {μ : ℕ → ℤ} {key key' : ℕ → ℕ} {N M offsets flat : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (he : ∀ i < N, key i=key' i) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key' N M offsets flat := by
  refine ⟨?_,?_⟩
  · intro r hr
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.offset_congr he]
    exact H.offsets r hr
  · intro i hi
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.position_congr he hi]
    exact H.indices i hi





end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One actual original-band histogram, buckets, and six pointer headers -/

namespace ThreeSum.LightSourceBandStep
open _root_.ThreeSum.LightSourceBandStep


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000














variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem original_time_le (n g p m U D i : ℕ) :
    _root_.ThreeSum.LightSourceBucketOriginal.time (_root_.ThreeSum.SourceBandLayout.len n g i) p m U D ≤ _root_.ThreeSum.LightSourceBandStep.charge n g p m U D := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal.time_bound (_root_.ThreeSum.SourceBandLayout.len n g i) p m U D
  apply ht.trans
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 498 (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap n g i))) (233*m)) 333





end ThreeSum.LightSourceBandStep

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBandStep
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tail_ends__implementation_5068d22c67 {pOriginal : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketOriginal.Procs P pOriginal)
    {μ : ℕ → ℤ} {src n g p m base U D i last : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hi : i < _root_.ThreeSum.BandPartition.size n g)
    (hsrc : src+n ≤ base) (hlast : last=_root_.ThreeSum.BandPartition.stop n g i)
    (hspace : _root_.ThreeSum.LightSourceResidues.space (_root_.ThreeSum.SourceBandLayout.work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tailBody pOriginal)
      ⟨_root_.Light.frame [src,n,g,p,m,shift,base,_root_.ThreeSum.SourceBandLayout.cap n g,_root_.ThreeSum.BandPartition.size n g,_root_.ThreeSum.SourceBandLayout.data base n g,_root_.ThreeSum.SourceBandLayout.stride n g m,
        _root_.ThreeSum.SourceBandLayout.work base n g m,i,_root_.ThreeSum.BandPartition.start g i,last],μ⟩
      (_root_.ThreeSum.LightSourceBandStep.tailTime n g p m U D) (fun σ =>
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At σ.mem f base n g p m shift i ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ σ.mem (_root_.ThreeSum.SourceBandLayout.hist base n g m i) (base+6*i) 6) := by
  subst last
  have hwork : _root_.ThreeSum.SourceBandLayout.work base n g m ≤ lim.space := by
    unfold _root_.ThreeSum.LightSourceResidues.space at hspace
    omega
  have hcap := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap n g i
  have hflat := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_work (base := base) (m := m) hi
  have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.header_end (base := base) (m := m) hi
  have hdata := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m i
  have hhist : _root_.ThreeSum.SourceBandLayout.hist base n g m i ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes at hflat
    omega
  have hb : base ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m i := by unfold _root_.ThreeSum.SourceBandLayout.data at hdata; omega
  have hstop := _root_.ThreeSum.BandPartition.stop_le n g i
  have hstart := _root_.ThreeSum.BandPartition.start_lt_stop hg hi
  have hlen := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.start_add_len hg hi
  have hprod : (i : ℤ)*(_root_.ThreeSum.SourceBandLayout.stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show i*_root_.ThreeSum.SourceBandLayout.stride n g m ≤ lim.space by unfold _root_.ThreeSum.SourceBandLayout.hist at hhist; omega) :
      (i : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  have hprodN : (0 : ℤ) ≤ (i : ℤ)*(_root_.ThreeSum.SourceBandLayout.stride n g m : ℤ) := by positivity
  have hheadprod : (6 : ℤ)*(i : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show 6*i ≤ lim.space by omega) : (6 : ℤ)*(i : ℤ) ≤ lim.space).trans hw
  have hcodes : _root_.ThreeSum.SourceBandLayout.codes base n g m i ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets at hflat
    omega
  have hoffsets : _root_.ThreeSum.SourceBandLayout.offsets base n g m i ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor at hflat
    omega
  have hcursor : _root_.ThreeSum.SourceBandLayout.cursor base n g m i ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by unfold _root_.ThreeSum.SourceBandLayout.flat at hflat; omega
  have hhistAddr : (_root_.ThreeSum.SourceBandLayout.data base n g : ℤ)+(i : ℤ)*(_root_.ThreeSum.SourceBandLayout.stride n g m : ℤ) ≤ lim.word :=
    (by exact_mod_cast (hhist.trans hwork) :
      (data base n g : ℤ)+(i : ℤ)*(stride n g m : ℤ) ≤ lim.space).trans hw
  have hcodesAddr : _root_.ThreeSum.SourceBandLayout.hist base n g m i+m ≤ lim.space := hcodes.trans hwork
  have hoffsetsAddr : _root_.ThreeSum.SourceBandLayout.codes base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g ≤ lim.space := hoffsets.trans hwork
  have hcursorAddr : _root_.ThreeSum.SourceBandLayout.offsets base n g m i+m+1 ≤ lim.space := hcursor.trans hwork
  have hflatAddr : _root_.ThreeSum.SourceBandLayout.cursor base n g m i+m ≤ lim.space := by unfold _root_.ThreeSum.SourceBandLayout.flat at hflat; omega
  have hword' : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.LightSourceResidues.word p m U D ≤ _root_.ThreeSum.LightSourceBandStep.word n g p m U D by
      unfold _root_.ThreeSum.LightSourceBandStep.word; omega)).trans hword
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tailBody _root_.ThreeSum.LightSourceBandStep.tailTime
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.len n g i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.len]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.len] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.len] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.hist base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.hist]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.hist] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.hist] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.codes base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.codes]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.codes] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.codes] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.offsets base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.offsets]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.offsets] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.offsets] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.cursor base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.cursor]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.cursor] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.cursor] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.flat base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.SourceBandLayout.flat]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.SourceBandLayout.flat] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.SourceBandLayout.flat] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have horiginal := C.meets (d := d+1) (μ := μ) (src := src+_root_.ThreeSum.BandPartition.start g i) (N := _root_.ThreeSum.SourceBandLayout.len n g i)
    (p := p) (m := m) (shift := shift) (hist := _root_.ThreeSum.SourceBandLayout.hist base n g m i) (codes := _root_.ThreeSum.SourceBandLayout.codes base n g m i)
    (offsets := _root_.ThreeSum.SourceBandLayout.offsets base n g m i) (cursor := _root_.ThreeSum.SourceBandLayout.cursor base n g m i) (flat := _root_.ThreeSum.SourceBandLayout.flat base n g m i)
    (work := _root_.ThreeSum.SourceBandLayout.work base n g m) (U := U) (D := D) hw (by omega) hp hm (by omega)
    le_rfl (by unfold _root_.ThreeSum.SourceBandLayout.offsets; omega) le_rfl le_rfl (by omega) hspace hshift hword'
    (by
      intro j hj
      have hj' := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hi hj
      rw [Nat.add_assoc,hread _ hj']
      exact hvalues _ hj')
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((horiginal.mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.original_time_le n g p m U D i)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (horiginal.mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.original_time_le n g p m U D i)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro r ν ⟨buckets, counts, keys, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i) (_root_.ThreeSum.BandPartition.start g i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i + 1) (_root_.ThreeSum.SourceBandLayout.len n g i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i + 2) (_root_.ThreeSum.SourceBandLayout.codes base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i + 3) (_root_.ThreeSum.SourceBandLayout.hist base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i + 4) (_root_.ThreeSum.SourceBandLayout.offsets base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 6 * i + 5) (_root_.ThreeSum.SourceBandLayout.flat base n g m i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  dsimp only
  have hkey : ∀ j < _root_.ThreeSum.SourceBandLayout.len n g i,
      _root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+_root_.ThreeSum.BandPartition.start g i+j))=_root_.ThreeSum.SourceBandLayout.key f g p m shift i j := by
    intro j hj
    rw [Nat.add_assoc,hread _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hi hj)]
    rfl
  have stored := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.buckets_congr buckets hkey
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,⟨?_,?_⟩⟩,?_⟩
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self ..
  · intro j hj
    have ha : base+6*i+6 ≤ _root_.ThreeSum.SourceBandLayout.codes base n g m i+j := by unfold _root_.ThreeSum.SourceBandLayout.codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keys j hj).trans (congrArg Int.ofNat (hkey j hj))
  · intro q hq
    repeat' rw [Function.update_of_ne (by omega)]
    exact (counts q hq).trans (congrArg Int.ofNat (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.count_congr hkey le_rfl q))
  · intro q hq
    have ha : base+6*i+6 ≤ _root_.ThreeSum.SourceBandLayout.offsets base n g m i+q := by unfold _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes; omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.offsets q hq
  · intro j hj
    have ha : base+6*i+6 ≤ _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBuckets.position (_root_.ThreeSum.SourceBandLayout.key f g p m shift i) (_root_.ThreeSum.SourceBandLayout.len n g i) j := by
      unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes
      omega
    repeat' rw [Function.update_of_ne (by omega)]
    exact stored.indices j hj
  · intro x hx
    repeat' rw [Function.update_of_ne (by omega)]
    exact kept x hx.1
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tail_ends__implementation_5068d22c67) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandStep.tail_ends__implementation_5068d22c67)

#print axioms solution
