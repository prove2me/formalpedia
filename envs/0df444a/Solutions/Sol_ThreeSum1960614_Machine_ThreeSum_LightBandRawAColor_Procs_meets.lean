-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:56:27.056528+00:00
-- url     : https://prove2.me/submissions/796ec2ee-34fb-449f-bc09-e7d3c0012214

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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandRawACatalog_Procs_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_tables_keep
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorBands_Procs_meets

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
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightBandCandidates
end ThreeSum.LightBandCandidates
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightBandRawA
end ThreeSum.LightBandRawA
namespace ThreeSum.LightBandRawACatalog
end ThreeSum.LightBandRawACatalog
namespace ThreeSum.LightBandRawAColor
end ThreeSum.LightBandRawAColor
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
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
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidates
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidates
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawA
end ThreeSum1960614.Machine.ThreeSum.LightBandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog
end ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































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
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

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

























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# All actual flagged band-owner records

The fixed program reads the three retained rectangular lookup tables and
writes one four-cell record for each cell, in the same BC, AB, AC order.
The record position is its permanent owner-slot identity.
-/

namespace ThreeSum.LightBandCandidates
open _root_.ThreeSum.LightBandCandidates


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}









theorem time_bound (a b c : ℕ) :
    _root_.ThreeSum.LightBandCandidates.time a b c ≤ 1000*(_root_.ThreeSum.LightBandEnumeration.count a b c+a+b+c+1) := by
  unfold _root_.ThreeSum.LightBandCandidates.time _root_.ThreeSum.LightBandCandidatesTable.time _root_.ThreeSum.LightBandCandidatesRow.time
    _root_.ThreeSum.LightBandCandidatesCell.time _root_.ThreeSum.LightBandEnumeration.count
  nlinarith

end ThreeSum.LightBandCandidates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual flattened A-incidence catalog

The loop reads each four-cell owner record once. Successful records append
only their actual truncated A band. Parallel value, owner-slot, and sorted
position arrays are packed using capacity g times the owner count.
-/

namespace ThreeSum.LightBandRawA
open _root_.ThreeSum.LightBandRawA


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000














variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {f : ℕ → ℤ}











theorem time_bound (N g : ℕ) : _root_.ThreeSum.LightBandRawA.time N g ≤ 1000*(N+1)*(g+1) := by
  unfold _root_.ThreeSum.LightBandRawA.time _root_.ThreeSum.LightBandRawAStep.time _root_.ThreeSum.LightBandRawARow.time _root_.Light.copyTime _root_.Light.fillTime
  nlinarith

end ThreeSum.LightBandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Read the retained headers, build owner records, and extract A incidences

The fixed program reads the actual sorted-A length and all three actual
band counts from the retained headers. It constructs the exact physical
BC, AB, AC records, then copies their flagged A bands into the three packed
value/owner/position arrays. No supplied enumeration or hidden input list
is used by either machine loop.
-/

namespace ThreeSum.LightBandRawACatalog
open _root_.ThreeSum.LightBandRawACatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

set_option maxHeartbeats 2100000
set_option maxRecDepth 8000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}









theorem time_bound (a b c g : ℕ) :
    _root_.ThreeSum.LightBandRawACatalog.time a b c g ≤ 3000*(_root_.ThreeSum.LightBandEnumeration.count a b c+a+b+c+1)*(g+1) := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.time_bound a b c
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.time_bound (_root_.ThreeSum.LightBandEnumeration.count a b c) g
  unfold _root_.ThreeSum.LightBandRawACatalog.time
  nlinarith

end ThreeSum.LightBandRawACatalog

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandRawAColor
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs.meets__implementation_43fcb7dd9a
    {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : ℕ}
    {μ : ℕ → ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs P pMain) (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (htable : work+_root_.ThreeSum.ColorBandBounds.count n g ≤ rec)
    (hrec : rec+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ vals)
    (hspace : _root_.ThreeSum.LightBandRawAColor.space work vals W n g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandRawAColor.word W n g U : ℤ) ≤ lim.word) (hd : d+_root_.ThreeSum.LightBandRawAColor.depth W n g ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work,rec,vals] μ (_root_.ThreeSum.LightBandRawAColor.time W n g)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Output ν av ae bv be cv ce work rec vals g hg
        (_root_.ThreeSum.ColorClassLists.classList p x 0 1) (_root_.ThreeSum.ColorClassLists.classList p x 1 1) (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)) r ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ ν colors) := by
  have hcSpace := (Nat.le_max_left (_root_.ThreeSum.LightColorBands.space work W n g)
    (_root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.ColorBandBounds.count n g) g)).trans hspace
  have hrSpace := (Nat.le_max_right (_root_.ThreeSum.LightColorBands.space work W n g)
    (_root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.ColorBandBounds.count n g) g)).trans hspace
  have hcWord : (_root_.ThreeSum.LightColorBands.word W n g U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.LightColorBands.word W n g U ≤ _root_.ThreeSum.LightBandRawAColor.word W n g U by
      unfold _root_.ThreeSum.LightBandRawAColor.word; omega)).trans hword
  have hcDepth : d+1+_root_.ThreeSum.LightColorBands.depth W n g ≤ lim.depth := by
    unfold _root_.ThreeSum.LightBandRawAColor.depth at hd; omega
  have hrDepth : d+1+3 < lim.depth := by unfold _root_.ThreeSum.LightBandRawAColor.depth at hd; omega
  have len0 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 0 1
  have len1 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 1 1
  have len2 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 2 (-1)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.body _root_.ThreeSum.LightBandRawAColor.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce hcSpace hcWord hcDepth hread hbound) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.color.meets (d := d + 1) p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce hcSpace hcWord hcDepth hread hbound) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro colorResult ν₁ ⟨hout, hkeepColor⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  obtain ⟨A,hsA,B,hsB,C,hsC,hcolorResult,hrepA,hrepB,hrepC,htables⟩ := hout
  let aFamily := _root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA)
  let bFamily := _root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB)
  let cFamily := _root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)
  have hnA : A.length ≤ n := hrepA.2.1.trans len0
  have hnB : B.length ≤ n := hrepB.2.1.trans len1
  have hnC : C.length ≤ n := hrepC.2.1.trans len2
  have ha : aFamily.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnA
  have hb : bFamily.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnB
  have hc : cFamily.size ≤ _root_.ThreeSum.BandPartition.size n g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hnC
  have hcount : _root_.ThreeSum.LightBandEnumeration.count aFamily.size bFamily.size cFamily.size ≤
      _root_.ThreeSum.ColorBandBounds.count n g := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.count_mono ha hb hc
    have heq : _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size n g) (_root_.ThreeSum.BandPartition.size n g) (_root_.ThreeSum.BandPartition.size n g) =
        _root_.ThreeSum.ColorBandBounds.count n g := by unfold _root_.ThreeSum.LightBandEnumeration.count _root_.ThreeSum.ColorBandBounds.count; ring
    rwa [heq] at hh
  have hcatSpace : _root_.ThreeSum.LightBandRawACatalog.space vals aFamily.size bFamily.size cFamily.size g ≤
      lim.space := by
    have hm := Nat.mul_le_mul_left g hcount
    unfold _root_.ThreeSum.LightBandRawACatalog.space _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase
      _root_.ThreeSum.LightBandRawA.ownerBase _root_.ThreeSum.LightBandRawA.capacity at hrSpace ⊢
    omega
  have hcatWord : (_root_.ThreeSum.LightBandRawACatalog.word A.length aFamily.size bFamily.size cFamily.size g : ℤ) ≤
      lim.word := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.count_mono ha hb hc
    apply (Int.ofNat_le.mpr (show _root_.ThreeSum.LightBandRawACatalog.word A.length aFamily.size bFamily.size
        cFamily.size g ≤ _root_.ThreeSum.LightBandRawAColor.word W n g U by
      unfold _root_.ThreeSum.LightBandRawAColor.word _root_.ThreeSum.LightBandRawACatalog.word _root_.ThreeSum.LightBandCandidates.word _root_.ThreeSum.LightBandRawA.word
      omega)).trans hword
  have hcatTime : _root_.ThreeSum.LightBandRawACatalog.time aFamily.size bFamily.size cFamily.size g ≤
      _root_.ThreeSum.LightBandRawAColor.catalogTime n g := by
    apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.time_bound _ _ _ _).trans
    unfold _root_.ThreeSum.LightBandRawAColor.catalogTime
    exact Nat.mul_le_mul_right (g+1) (Nat.mul_le_mul_left 3000 (by omega))
  have hsource : ∀ j < A.length, ν₁ (av+j)=A.getD j 0 := by
    intro j hj
    exact hrepA.1.getD hj 0
  have hcat := R.catalog.meets (d := d+1) (tables := work) (rec := rec) (src := av)
    (headerA := ae) (headerB := be) (headerC := ce) (vals := vals)
    aFamily bFamily cFamily rfl hw hrDepth hg (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hcatSpace hcatWord
    hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 htables hsource
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hcat.mono_time hcatTime) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcat.mono_time hcatTime) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro result ν₂ ⟨hresult, hrecords, hstored, hkeepCatalog⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsA) hrepA hkeepCatalog (by omega) (by omega),
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsB) hrepB hkeepCatalog (by omega) (by omega),
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsC) hrepC hkeepCatalog (by omega) (by omega),
    _root_.ThreeSum.LightBandRawAColor.tables_keep (A := aFamily) (B := bFamily) (C := cFamily)
      htables hkeepCatalog (by omega),hrecords,?_⟩,?_⟩
  · simpa only [_root_.ThreeSum.BandRawA.sortedRecords,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length] using hstored
  · intro a ha'
    change ν₂ a=μ a
    exact (hkeepCatalog a (by omega)).trans (hkeepColor a ha')
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs.meets__implementation_43fcb7dd9a) := (@ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.Procs.meets__implementation_43fcb7dd9a)

#print axioms solution
