-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized.keep
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:50:17.596864+00:00
-- url     : https://prove2.me/submissions/3efafdb5-1902-416e-9bc9-43b472bddcc5

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
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
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightBandRawAColor_tables_keep

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition








theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega











theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]









/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)











































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration
open _root_.ThreeSum.LightBandEnumeration


set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}












































theorem count_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.count a b c ≤ _root_.ThreeSum.LightBandEnumeration.count a' b' c' := by
  unfold _root_.ThreeSum.LightBandEnumeration.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)





end ThreeSum.LightBandEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ## Limits -/









/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



























theorem rect_length (m n : ℕ) (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.rect m n F).length=m*n := by
  simp [_root_.ThreeSum.BandCandidateRows.rect,List.length_flatMap]

theorem records_length (A B C : _root_.ThreeSum.BandEnumeration.Family) :
    (_root_.ThreeSum.BandCandidateRows.records A B C).length=_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size := by
  simp only [_root_.ThreeSum.BandCandidateRows.records,List.length_append,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length,_root_.ThreeSum.LightBandEnumeration.count]
  omega

theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000



















theorem row_length (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) :
    (_root_.ThreeSum.BandRawA.row n g owner r).length=if r.flag=1 then _root_.ThreeSum.BandRawA.bandLength n g r.a else 0 := by
  unfold _root_.ThreeSum.BandRawA.row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.row n g owner r).length ≤ g := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length]
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g r.a
  · omega





theorem firstRows_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.firstRows n g rs (i+1)=_root_.ThreeSum.BandRawA.firstRows n g rs i++_root_.ThreeSum.BandRawA.row n g i (rs.getD i default) := by
  simp only [_root_.ThreeSum.BandRawA.firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]



theorem count_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.count n g rs (i+1)=_root_.ThreeSum.BandRawA.count n g rs i+(_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)).length := by
  simp only [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.firstRows_succ,List.length_append]



theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum.BandRawA.firstRows]
  | succ i ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ]
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.items n g rs).length ≤ g*rs.length :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_bound n g rs rs.length


theorem ownerLabels_length (ls : List _root_.ThreeSum.BandRawA.Label) : (_root_.ThreeSum.BandRawA.ownerLabels ls).length=ls.length := List.length_map ..
theorem positionLabels_length (ls : List _root_.ThreeSum.BandRawA.Label) : (_root_.ThreeSum.BandRawA.positionLabels ls).length=ls.length := List.length_map ..



















end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The three retained parallel arrays of A-value incidences -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1400000













theorem Stored.of_kept {μ ν : ℕ → ℤ} {vals owners positions fr : ℕ}
    {f : ℕ → ℤ} {ls : List _root_.ThreeSum.BandRawA.Label} (H : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions f ls)
    (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ ν fr) (hv : vals+ls.length ≤ fr)
    (ho : owners+ls.length ≤ fr) (hp : positions+ls.length ≤ fr) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals owners positions f ls :=
  ⟨H.valueRows.of_kept hk (by simpa only [_root_.ThreeSum.BandRawA.values_length] using hv),
    H.ownerRows.of_kept hk (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.ownerLabels_length] using ho),
    H.positionRows.of_kept hk (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.positionLabels_length] using hp)⟩

end ThreeSum.BandRawA

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
section


theorem ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized.keep__implementation_9181522416 {μ ν : ℕ → ℤ} {av ae bv be cv ce tables rec vals g n bound : ℕ}
    {hg : 0 < g} {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r)
    (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ bound) (hae : ae+2+2*n ≤ bound)
    (hbv : bv+n ≤ bound) (hbe : be+2+2*n ≤ bound)
    (hcv : cv+n ≤ bound) (hce : ce+2+2*n ≤ bound)
    (htables : tables+_root_.ThreeSum.ColorBandBounds.count n g ≤ bound)
    (hrecords : rec+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ bound)
    (hcatalog : _root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.ColorBandBounds.count n g) g ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := by
  obtain ⟨hr,repA,repB,repC,tablesAt,recordRows,incidences⟩ := H
  have hnA := repA.2.1.trans hA
  have hnB := repB.2.1.trans hB
  have hnC := repC.2.1.trans hC
  let FA := _root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA)
  let FB := _root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB)
  let FC := _root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)
  let rs := _root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC
  have ha : FA.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnA
  have hb : FB.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnB
  have hc : FC.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnC
  have hcount : _root_.ThreeSum.LightBandEnumeration.count FA.size FB.size FC.size ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
    have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.count_mono ha hb hc
    have he : _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size n g) (_root_.ThreeSum.BandPartition.size n g) (_root_.ThreeSum.BandPartition.size n g)=_root_.ThreeSum.ColorBandBounds.count n g := by
      unfold _root_.ThreeSum.LightBandEnumeration.count _root_.ThreeSum.ColorBandBounds.count
      ring
    rwa [he] at hm
  have hlen : rs.length ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
    simpa only [rs,_root_.ThreeSum.BandRawA.sortedRecords,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length,FA,FB,FC] using hcount
  have hitems : (_root_.ThreeSum.BandRawA.items A.length g rs).length ≤ g*rs.length := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.items_length_le ..
  have hgc := Nat.mul_le_mul_left g hlen
  have hfour := Nat.mul_le_mul_left 4 hlen
  dsimp only [rs] at hitems hgc
  refine ⟨hr,_root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsA) repA hk (by omega) (by omega),_root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsB) repB hk (by omega) (by omega),
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsC) repC hk (by omega) (by omega),?_,?_,?_⟩
  · exact _root_.ThreeSum.LightBandRawAColor.tables_keep tablesAt hk ((Nat.add_le_add_left hcount tables).trans htables)
  · exact recordRows.of_kept hk (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length] using (show rec+4*rs.length ≤ bound by omega))
  · apply incidences.of_kept hk
    all_goals
      change _ ≤ bound
      simp only [_root_.ThreeSum.LightBandRawA.space,_root_.ThreeSum.LightBandRawA.positionBase,_root_.ThreeSum.LightBandRawA.ownerBase,_root_.ThreeSum.LightBandRawA.capacity] at hcatalog ⊢
      omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized.keep__implementation_9181522416) := (@ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Normalized.keep__implementation_9181522416)

#print axioms solution
