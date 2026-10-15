-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:24.916825+00:00
-- url     : https://prove2.me/submissions/2c5d0ee5-79c3-4b77-b9d8-33156f4b49ee

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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidates_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandRawA_Procs_meets
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightBandRawA
end ThreeSum.LightBandRawA
namespace ThreeSum.LightBandRawACatalog
end ThreeSum.LightBandRawACatalog
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawA
end ThreeSum1960614.Machine.ThreeSum.LightBandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog
end ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000



theorem records_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  exact _root_.ThreeSum.BandCandidateRows.fromOwner_sound A B C o hf



theorem getD_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {s : ℕ} (hs : s < (_root_.ThreeSum.BandCandidateRows.records A B C).length)
    (hf : ((_root_.ThreeSum.BandCandidateRows.records A B C).getD s default).flag=1) :
    let r := (_root_.ThreeSum.BandCandidateRows.records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_sound _ hf
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs









end ThreeSum.BandCandidateRows

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









/-- The physical candidate list supplies every successful A-index validity
fact required by the actual incidence loop. -/
theorem Procs.meets_candidates {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawA.Procs P pMain)
    (A B C : _root_.ThreeSum.BandEnumeration.Family) (hA : A.size=_root_.ThreeSum.BandPartition.size n g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hg : 0 < g)
    (hrecords : records+4*(_root_.ThreeSum.BandCandidateRows.records A B C).length ≤ vals)
    (hsrc : src+n ≤ vals)
    (hspace : _root_.ThreeSum.LightBandRawA.space vals (_root_.ThreeSum.BandCandidateRows.records A B C).length g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandRawA.word n g (_root_.ThreeSum.BandCandidateRows.records A B C).length : ℤ) ≤ lim.word)
    (hrecordRead : _root_.ThreeSum1960614.Machine.Light.Seg μ records (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.records A B C)))
    (hread : ∀ j < n, μ (src+j)=f j) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [records,(_root_.ThreeSum.BandCandidateRows.records A B C).length,src,n,g,vals]
      μ (_root_.ThreeSum.LightBandRawA.time (_root_.ThreeSum.BandCandidateRows.records A B C).length g)
      (fun r ν => r=((_root_.ThreeSum.BandRawA.items n g (_root_.ThreeSum.BandCandidateRows.records A B C)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals (_root_.ThreeSum.LightBandRawA.ownerBase vals (_root_.ThreeSum.BandCandidateRows.records A B C).length g)
          (_root_.ThreeSum.LightBandRawA.positionBase vals (_root_.ThreeSum.BandCandidateRows.records A B C).length g)
          f (_root_.ThreeSum.BandRawA.items n g (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν vals) := by
  apply S.meets hw hd hg hrecords hsrc hspace hword _ hrecordRead hread
  intro i hi hf
  simpa only [hA] using (_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.getD_sound hi hf).1



end ThreeSum.LightBandRawA

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandRawACatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog

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
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets__implementation_92de435a6a {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hA : A.size=_root_.ThreeSum.BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth) (hg : 0 < g)
    (htable : tables+_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ rec)
    (hsrc : src+nA ≤ rec) (hheadA : headerA+2 ≤ rec)
    (hheadB : headerB+2 ≤ rec) (hheadC : headerC+2 ≤ rec)
    (hrec : rec+4*_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : _root_.ThreeSum.LightBandRawACatalog.space vals A.size B.size C.size g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandRawACatalog.word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerA nA A)
    (hheaderB : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerB nB B)
    (hheaderC : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerC nC C)
    (htables : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src+j)=f j) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [tables,rec,src,headerA,headerB,headerC,g,vals]
      μ (_root_.ThreeSum.LightBandRawACatalog.time A.size B.size C.size g)
      (fun r ν => r=((_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν rec (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals (_root_.ThreeSum.LightBandRawA.ownerBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          (_root_.ThreeSum.LightBandRawA.positionBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          f (_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν rec) := by
  have hvals : vals ≤ lim.space := by
    unfold _root_.ThreeSum.LightBandRawACatalog.space _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase at hspace
    omega
  have hcandidateSpace : _root_.ThreeSum.LightBandCandidates.space rec A.size B.size C.size ≤ lim.space := by
    unfold _root_.ThreeSum.LightBandCandidates.space
    omega
  have hcandidateWord : (_root_.ThreeSum.LightBandCandidates.word A.size B.size C.size : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawACatalog.word; omega :
      LightBandCandidates.word A.size B.size C.size ≤ word nA A.size B.size C.size g)).trans hword
  have hrawWord : (_root_.ThreeSum.LightBandRawA.word nA g (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandRawACatalog.word; omega :
      LightBandRawA.word nA g (LightBandEnumeration.count A.size B.size C.size) ≤
        word nA A.size B.size C.size g)).trans hword
  have h1Word : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ _root_.ThreeSum.LightBandRawACatalog.word nA A.size B.size C.size g := by unfold _root_.ThreeSum.LightBandRawACatalog.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnRead := hheaderA.1
  have haRead := hheaderA.2.1
  have hbRead := hheaderB.2.1
  have hcRead := hheaderC.2.1
  have haAddr : ((headerA : ℤ)+1).toNat=headerA+1 := by omega
  have hbAddr : ((headerB : ℤ)+1).toNat=headerB+1 := by omega
  have hcAddr : ((headerC : ℤ)+1).toNat=headerC+1 := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.body _root_.ThreeSum.LightBandRawACatalog.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (nA : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hnRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hnRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hnRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (A.size : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haAddr, haRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [haAddr, haRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haAddr, haRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (B.size : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbAddr, hbRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbAddr, hbRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbAddr, hbRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (C.size : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcAddr, hcRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcAddr, hcRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcAddr, hcRead] <;> omega)
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
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.candidates.meets (d := d + 1) A B C hw (by omega) htable hcandidateSpace hcandidateWord htables) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.candidates.meets (d := d + 1) A B C hw (by omega) htable hcandidateSpace hcandidateWord htables) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro countResult ν₁ ⟨hcount, hrecords, hkeepCandidates⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hsource : ∀ j < nA, ν₁ (src+j)=f j := by
    intro j hj
    rw [hkeepCandidates _ (Or.inl (by omega))]
    exact hread j hj
  have hraw := S.raw.meets_candidates (d := d+1) (records := rec) (src := src)
    (vals := vals) (n := nA) (g := g) (f := f) A B C hA hw (by omega) hg
    (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length] using hrec) (by omega)
    (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length,_root_.ThreeSum.LightBandRawACatalog.space] using hspace)
    (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length] using hrawWord) hrecords hsource
  have hraw' : _root_.ThreeSum1960614.Machine.Light.Meets lim P S.pRaw (d+1)
      [rec,_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size,src,nA,g,vals] ν₁
      (_root_.ThreeSum.LightBandRawA.time (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
      (fun r ν => r=((_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals (_root_.ThreeSum.LightBandRawA.ownerBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          (_root_.ThreeSum.LightBandRawA.positionBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          f (_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν₁ ν vals) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length] using hraw
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hraw' _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hraw' ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcount] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega)
     on_goal -1 => (rintro result ν₂ ⟨hresult, hstored, hkeepRaw⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hresult,?_,hstored,?_⟩
  · exact hrecords.of_kept hkeepRaw (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length] using hrec)
  · intro addr ha
    change ν₂ addr=μ addr
    rw [hkeepRaw addr (by omega),hkeepCandidates addr (Or.inl ha)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets__implementation_92de435a6a) := (@ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets__implementation_92de435a6a)

#print axioms solution
