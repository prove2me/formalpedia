-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:21:50.703313+00:00
-- url     : https://prove2.me/submissions/257d360c-8bc3-433d-9381-a3d3d6a0dcdb

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWantedRow_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedPairs_row_segment
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective

private theorem platform_seg_append_83d39ab9f3 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_83d39ab9f3 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightWantedJoin
end ThreeSum.LightWantedJoin
namespace ThreeSum.SourceBucketView
end ThreeSum.SourceBucketView
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
end ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
namespace ThreeSum1960614.Machine.ThreeSum.SourceBucketView
end ThreeSum1960614.Machine.ThreeSum.SourceBucketView
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/















theorem Ends.ite {σ T c s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hv he, by omega, hq⟩













/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/























/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.ite _ hs h₁ h₂ (by omega)





/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







end Light

end

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







theorem exists_position {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M)
    {t : ℕ} (ht : t < N) : ∃ i < N, _root_.ThreeSum.SourceBuckets.position key N i = t := by
  let f : Fin N → Fin N := fun i => ⟨_root_.ThreeSum.SourceBuckets.position key N i.val,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_lt hkey i.isLt⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (_root_.ThreeSum.SourceBuckets.position_injective i.isLt j.isLt (congrArg Fin.val he))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective hf ⟨t,ht⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

theorem exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < _root_.ThreeSum.LightHistogram.count key r N) :
    ∃ i < N, key i = r ∧ _root_.ThreeSum.SourceBuckets.position key N i = _root_.ThreeSum.SourceBuckets.offset key N r+t := by
  have htN : _root_.ThreeSum.SourceBuckets.offset key N r+t < N := by
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (show r+1 ≤ M by omega)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (_root_.ThreeSum.SourceBuckets.position_bucket_iff hi).mp
  rw [he,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  omega





theorem bucketList_length (μ : ℕ → ℤ) (flat start length : ℕ) :
    (_root_.ThreeSum.SourceBuckets.bucketList μ flat start length).length = length := by simp [_root_.ThreeSum.SourceBuckets.bucketList]

theorem Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < _root_.ThreeSum.LightHistogram.count key r N) :
    ∃ i < N, key i = r ∧ _root_.ThreeSum.SourceBuckets.position key N i = _root_.ThreeSum.SourceBuckets.offset key N r+t ∧
      μ (flat+_root_.ThreeSum.SourceBuckets.offset key N r+t) = (i : ℤ) := by
  obtain ⟨i,hi,hki,hpos⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.exists_bucket_position hkey hr ht
  refine ⟨i,hi,hki,hpos,?_⟩
  simpa only [hpos,Nat.add_assoc] using H.indices i hi







end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView
open _root_.ThreeSum.SourceBucketView


open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram






theorem start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBucketView.start μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N r := by
  simp only [_root_.ThreeSum.SourceBucketView.start,H.offsets r hr,Int.toNat_natCast]

theorem stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.stop μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N (r+1) := by
  unfold _root_.ThreeSum.SourceBucketView.stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]

theorem length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.length μ offsets r = _root_.ThreeSum.LightHistogram.count key r N := by
  rw [_root_.ThreeSum.SourceBucketView.length,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.stop_eq H hr,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  omega

theorem indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.indices μ offsets flat r = _root_.ThreeSum.SourceBuckets.bucketList μ flat (_root_.ThreeSum.SourceBuckets.offset key N r) (_root_.ThreeSum.LightHistogram.count key r N) := by
  rw [_root_.ThreeSum.SourceBucketView.indices,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.length_eq H hr]

theorem indices_length {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    (_root_.ThreeSum.SourceBucketView.indices μ offsets flat r).length = _root_.ThreeSum.LightHistogram.count key r N := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.indices_eq H hr,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.bucketList_length]









end ThreeSum.SourceBucketView

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs
open _root_.ThreeSum.WantedPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open scoped _root_.BigOperators

set_option maxHeartbeats 1200000



@[simp] theorem count_zero (left right : ℕ → ℕ) (NR : ℕ) : _root_.ThreeSum.WantedPairs.count left right NR 0=0 := by
  simp [_root_.ThreeSum.WantedPairs.count]

theorem count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    _root_.ThreeSum.WantedPairs.count left right NR (n+1)=_root_.ThreeSum.WantedPairs.count left right NR n+_root_.ThreeSum.LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _

theorem count_mono (left right : ℕ → ℕ) (NR : ℕ) : Monotone (_root_.ThreeSum.WantedPairs.count left right NR) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)







theorem pairs_succ (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.WantedPairs.pairs μ offsets flat left (n+1)=_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n++_root_.ThreeSum.WantedPairs.row μ offsets flat left n := by
  simp only [_root_.ThreeSum.WantedPairs.pairs,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

theorem row_length {μ : ℕ → ℤ} {offsets flat NR M i : ℕ} {left right : ℕ → ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) (hi : left i < M) :
    (_root_.ThreeSum.WantedPairs.row μ offsets flat left i).length=_root_.ThreeSum.LightHistogram.count right (left i) NR := by
  rw [_root_.ThreeSum.WantedPairs.row,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.indices_length H hi]

theorem pairs_length {μ : ℕ → ℤ} {offsets flat NR M : ℕ} {left right : ℕ → ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) : ∀ n,
    (∀ i < n, left i < M) →
      (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n).length=_root_.ThreeSum.WantedPairs.count left right NR n := by
  intro n
  induction n with
  | zero => intro _; simp [_root_.ThreeSum.WantedPairs.pairs]
  | succ n ih =>
    intro hleft
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_succ,List.length_append,ih (fun i hi => hleft i (by omega)),
      _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.row_length H (hleft n (by omega)),_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.count_succ]









theorem cells_append (as bs : List (ℕ × ℕ)) : _root_.ThreeSum.WantedPairs.cells (as++bs)=_root_.ThreeSum.WantedPairs.cells as++_root_.ThreeSum.WantedPairs.cells bs :=
  List.flatMap_append ..











end ThreeSum.WantedPairs

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWantedJoin
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.WantedPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.meets__implementation_79665daa31 {pMain pRow keys offsets flat NR M dst : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.body pMain pRow))
    (hrow : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedRow.body)
    (left right : ℕ → ℕ) (hright : ∀ j < NR, right j < M) :
    ∀ n d : ℕ, ∀ μ : ℕ → ℤ,
      (lim.space : ℤ) ≤ lim.word → keys+n ≤ dst → offsets+M+1 ≤ dst → flat+NR ≤ dst →
      dst+2*_root_.ThreeSum.WantedPairs.count left right NR n ≤ lim.space → d+n+2 ≤ lim.depth →
      (∀ i < n, left i < M) → (∀ i < n, μ (keys+i)=(left i : ℤ)) →
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,offsets,flat,n,NR,M,dst] μ (_root_.ThreeSum.LightWantedJoin.time left right NR n)
        (fun r ν => r=(_root_.ThreeSum.WantedPairs.count left right NR n : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.WantedPairs.cells (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  intro n
  induction n with
  | zero =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.body _root_.ThreeSum.LightWantedJoin.time
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl,by simp [_root_.ThreeSum.WantedPairs.cells,_root_.ThreeSum.WantedPairs.pairs],fun _ _ => rfl⟩
  | succ n ih =>
    intro d μ hw hkeys hoffsets hflat hspace hd hleft hread H
    let previous := _root_.ThreeSum.WantedPairs.count left right NR n
    let size := _root_.ThreeSum.LightHistogram.count right (left n) NR
    let start := _root_.ThreeSum.SourceBuckets.offset right NR (left n)
    have htotal : _root_.ThreeSum.WantedPairs.count left right NR (n+1)=previous+size := _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.count_succ left right NR n
    have hspace' : dst+2*(previous+size) ≤ lim.space := by rwa [htotal] at hspace
    have hcode := hleft n (by omega)
    have hstart : start ≤ NR := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hright (by omega)
    have hend : start+size ≤ NR := by
      have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hright (show left n+1 ≤ M by omega)
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ] at hh
      exact hh
    have hprevious : previous ≤ _root_.ThreeSum.WantedPairs.count left right NR (n+1) := _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.count_mono left right NR (by omega)
    have hpreviousWord : (previous : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show previous ≤ lim.space by omega)).trans hw
    have hsizeWord : (size : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show size ≤ lim.space by omega)).trans hw
    apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.body _root_.ThreeSum.LightWantedJoin.time
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    have hprev := ih (d+1) μ hw (by omega) hoffsets hflat (by omega) (by omega)
      (fun i hi => hleft i (by omega)) (fun i hi => hread i (by omega)) H
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hprev _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hprev ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWantedRow.time] <;> omega)
       on_goal -1 => (rintro prev μ₁ ⟨hprev, hstored, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hreadCode : μ₁ (keys+n)=(left n : ℤ) :=
      (hkeep₁ _ (by omega)).trans (hread n (by omega))
    have hreadCodeZ : μ₁ (((keys : ℤ)+(n : ℤ)).toNat)=(left n : ℤ) := by
      rw [show ((keys : ℤ)+(n : ℤ)).toNat=keys+n by omega]
      exact hreadCode
    have hreadStart : μ₁ (offsets+left n)=(start : ℤ) :=
      (hkeep₁ _ (by omega)).trans (H.offsets (left n) (by omega))
    have hreadStartZ : μ₁ (((offsets : ℤ)+(left n : ℤ)).toNat)=(start : ℤ) := by
      rw [show ((offsets : ℤ)+(left n : ℤ)).toNat=offsets+left n by omega]
      exact hreadStart
    have hreadStop : μ₁ (offsets+left n+1)=((start+size : ℕ) : ℤ) := by
      rw [hkeep₁ _ (by omega),Nat.add_assoc,H.offsets (left n+1) (by omega),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
    have hreadStopZ : μ₁ (((offsets : ℤ)+(left n : ℤ)+1).toNat)=((start+size : ℕ) : ℤ) := by
      rw [show ((offsets : ℤ)+(left n : ℤ)+1).toNat=offsets+left n+1 by omega]
      exact hreadStop
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWantedRow.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (left n : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadCodeZ, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadCodeZ, _root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadCodeZ, _root_.ThreeSum.LightWantedRow.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (start : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadStartZ, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadStartZ, _root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadStartZ, _root_.ThreeSum.LightWantedRow.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (size : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadStopZ, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadStopZ, _root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadStopZ, _root_.ThreeSum.LightWantedRow.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hflatRead (t : ℕ) (ht : t < size) : μ₁ (flat+start+t)=μ (flat+start+t) :=
      hkeep₁ _ (by omega)
    have hrowValues (t : ℕ) (ht : t < size) : |μ₁ (flat+start+t)| ≤ lim.word := by
      obtain ⟨j,hj,_,_,hjRead⟩ := H.read_bucket hright hcode ht
      rw [hflatRead t ht,hjRead,Int.abs_natCast]
      exact (Int.ofNat_le.mpr (show j ≤ lim.space by omega)).trans hw
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedRow.meets (d := d+1) (μ := μ₁) (left := n) (src := flat)
      (start := start) (n := size) (dst := dst) (previous := previous)
      hrow hw (by omega) hspace'
      ((Int.ofNat_le.mpr (show n ≤ lim.space by omega)).trans hw) hrowValues
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hprev, previous, size, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hprev, previous, size, _root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hprev, previous, size, _root_.ThreeSum.LightWantedRow.time] <;> omega)
       on_goal -1 => (rintro unused μ₂ ⟨hout, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hnew : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ (dst+2*previous) (_root_.ThreeSum.WantedPairs.cells (_root_.ThreeSum.WantedPairs.row μ offsets flat left n)) := by
      apply _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.row_segment H hright hcode
      intro t ht
      exact ⟨(hout t ht).1,(hout t ht).2.trans (hflatRead t ht)⟩
    have holdLen : (_root_.ThreeSum.WantedPairs.cells (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n)).length=2*previous := by
      rw [_root_.ThreeSum.WantedPairs.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_length H n (fun i hi => hleft i (by omega))]
    have hold : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ dst (_root_.ThreeSum.WantedPairs.cells (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n)) :=
      hstored.of_sameOutside hkeep₂ (Or.inl (by rw [holdLen]))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.WantedPairs.count left right NR (n + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, htotal, hprev, previous, size, _root_.ThreeSum.LightWantedRow.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [htotal, hprev, previous, size, _root_.ThreeSum.LightWantedRow.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htotal, hprev, previous, size, _root_.ThreeSum.LightWantedRow.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨rfl,?_,?_⟩
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_succ,_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.cells_append]
      apply platform_seg_append_83d39ab9f3.mpr
      exact ⟨hold,by simpa only [holdLen] using hnew⟩
    · intro a ha
      change μ₂ a=μ a
      exact (hkeep₂ a (Or.inl (by omega))).trans (hkeep₁ a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.meets__implementation_79665daa31) := (@ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.meets__implementation_79665daa31)

#print axioms solution
