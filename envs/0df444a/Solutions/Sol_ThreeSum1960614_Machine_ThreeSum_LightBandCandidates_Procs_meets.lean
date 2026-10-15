-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:16.362778+00:00
-- url     : https://prove2.me/submissions/848000cb-626e-4991-b478-e4db41a067bc

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandCandidateRows_seg_rect
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidatesTable_meets
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound

private theorem platform_seg_append_f615a21baf {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_f615a21baf (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightBandCandidates
end ThreeSum.LightBandCandidates
namespace ThreeSum.LightBandCandidatesTable
end ThreeSum.LightBandCandidatesTable
namespace ThreeSum.LightBandLookup
end ThreeSum.LightBandLookup
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidates
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidates
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable
namespace ThreeSum1960614.Machine.ThreeSum.LightBandLookup
end ThreeSum1960614.Machine.ThreeSum.LightBandLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







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





















/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Division-free binary interval lookup in actual machine syntax

The search descends a constructed powers-of-two table and extends a known
prefix by one power at a time. Every tested endpoint is an explicit bounded
memory load. Neither natural-number division nor a function-valued memory
oracle is a machine operation. `search_meets` identifies its returned prefix
with any valid sorted partition, and hence with `BinarySearch.upperBound`.
-/

namespace ThreeSum.LightBandLookup
open _root_.ThreeSum.LightBandLookup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









theorem result_le (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j) : _root_.ThreeSum.LightBandLookup.result lo hi n x ≤ n := by
  unfold _root_.ThreeSum.LightBandLookup.result
  cases h : _root_.ThreeSum.BinarySearch.locate lo hi n x with
  | none => simp
  | some i =>
      have hh := _root_.ThreeSum.BinarySearch.locate_sound lo hi n x hsorted h
      simp only [Option.map_some,Option.getD_some]
      omega











end ThreeSum.LightBandLookup

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



theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega

theorem index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by
  have hh := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega





















end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual rectangular owner records with two nested loops -/

namespace ThreeSum.LightBandCandidatesTable
open _root_.ThreeSum.LightBandCandidatesTable


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}



theorem meets_segment {pMain pRow pCell : ℕ} (mode : _root_.ThreeSum.BandCandidateRows.Mode)
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.body pRow))
    (hrow : P[pRow]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hsrc : src+m*n ≤ dst) (hspace : dst+4*(m*n) ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word) (hm : m ≤ U) (hn : n ≤ U)
    (hf : ∀ i < m, ∀ j < n, f i j ≤ U)
    (hread : ∀ i < m, ∀ j < n, μ (src+i*n+j)=(f i j : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,m,n] μ (_root_.ThreeSum.LightBandCandidatesTable.time m n)
      (fun _ ν => _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect m n (fun i j => _root_.ThreeSum.BandCandidateRows.make mode i j (f i j)))) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*(m*n))) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.meets mode hmain hrow hcell hw hd hsrc hspace hword hm hn hf hread).mono le_rfl
    (fun _ _ h => ⟨_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_rect _ h.1,h.2⟩)



end ThreeSum.LightBandCandidatesTable

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandCandidates
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates

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
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets__implementation_a82d165fc8 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandCandidates.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandCandidates.word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ src A B C) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,A.size,B.size,C.size] μ (_root_.ThreeSum.LightBandCandidates.time A.size B.size C.size)
      (fun r ν => r=(_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size)) := by
  let U := A.size+B.size+C.size
  let bcN := B.size*C.size
  let abN := A.size*B.size
  let acN := A.size*C.size
  have hcount : _root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size=bcN+abN+acN := rfl
  have hsrc' : src+bcN+abN+acN ≤ dst := by simpa only [hcount,Nat.add_assoc] using hsrc
  have hspace' : dst+4*(bcN+abN+acN) ≤ lim.space := hspace
  have hAU : A.size ≤ U := by unfold U; omega
  have hBU : B.size ≤ U := by unfold U; omega
  have hCU : C.size ≤ U := by unfold U; omega
  have hwordU : ((U+10 : ℕ) : ℤ) ≤ lim.word := hword
  have hAWord : (A.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : A.size ≤ U+10)).trans hwordU
  have hBWord : (B.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : B.size ≤ U+10)).trans hwordU
  have hCWord : (C.size : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : C.size ≤ U+10)).trans hwordU
  have hbcWord : (B.size : ℤ)*(C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show bcN ≤ lim.space by omega) :
      (B.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have habWord : (A.size : ℤ)*(B.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show abN ≤ lim.space by omega) :
      (A.size : ℤ)*(B.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hacWord : (A.size : ℤ)*(C.size : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show acN ≤ lim.space by omega) :
      (A.size : ℤ)*(C.size : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hbcNonneg : (0 : ℤ) ≤ (B.size : ℤ)*(C.size : ℤ) := by positivity
  have habNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(B.size : ℤ) := by positivity
  have hacNonneg : (0 : ℤ) ≤ (A.size : ℤ)*(C.size : ℤ) := by positivity
  have hbcBound : ∀ j < B.size, ∀ k < C.size,
      _root_.ThreeSum.LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j) ≤ U := by
    intro j _ k _
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.result_le _ _ _ _ A.sorted).trans hAU
  have habBound : ∀ i < A.size, ∀ j < B.size,
      _root_.ThreeSum.LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) ≤ U := by
    intro i _ j _
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.result_le _ _ _ _ C.sorted).trans hCU
  have hacBound : ∀ i < A.size, ∀ k < C.size,
      _root_.ThreeSum.LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) ≤ U := by
    intro i _ k _
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.result_le _ _ _ _ B.sorted).trans hBU
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.body _root_.ThreeSum.LightBandCandidates.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bcN : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bcN]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [bcN] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bcN] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (abN : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, abN]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [abN] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, abN] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (acN : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, acN]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [acN] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, acN] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bcN + abN + acN : ℕ) ?_ ?_ ?_
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
  have hcBC := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.meets_segment (d := d+1) (μ := μ)
    (src := src) (dst := dst) _root_.ThreeSum.BandCandidateRows.Mode.bc S.bc S.rowBC S.cellBC hw (by omega)
    (by change src+bcN ≤ dst; omega) (by change dst+4*bcN ≤ lim.space; omega)
    hwordU hBU hCU hbcBound htables.1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcBC _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcBC ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;> omega)
     on_goal -1 => (rintro unused ν₁ ⟨hbc, hkeepBC⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have habRead : ∀ i < A.size, ∀ j < B.size,
      ν₁ (src+bcN+i*B.size+j)=
        (_root_.ThreeSum.LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j) : ℤ) := by
    intro i hi j hj
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.index_lt hi hj
    rw [hkeepBC _ (Or.inl (by change i*B.size+j < abN at hh; omega))]
    exact htables.2.1 i hi j hj
  have hcAB := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.meets_segment (d := d+1) (μ := ν₁)
    (src := src+bcN) (dst := dst+4*bcN) _root_.ThreeSum.BandCandidateRows.Mode.ab S.ab S.rowAB S.cellAB hw (by omega)
    (by change src+bcN+abN ≤ dst+4*bcN; omega)
    (by change dst+4*bcN+4*abN ≤ lim.space; omega)
    hwordU hAU hBU habBound habRead
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcAB _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcAB ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;> omega)
     on_goal -1 => (rintro unused ν₂ ⟨hab, hkeepAB⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hacRead : ∀ i < A.size, ∀ k < C.size,
      ν₂ (src+bcN+abN+i*C.size+k)=
        (_root_.ThreeSum.LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i) : ℤ) := by
    intro i hi k hk
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.index_lt hi hk
    rw [hkeepAB _ (Or.inl (by change i*C.size+k < acN at hh; omega)),
      hkeepBC _ (Or.inl (by change i*C.size+k < acN at hh; omega))]
    exact htables.2.2 i hi k hk
  have hcAC := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesTable.meets_segment (d := d+1) (μ := ν₂)
    (src := src+bcN+abN) (dst := dst+4*(bcN+abN)) _root_.ThreeSum.BandCandidateRows.Mode.ac S.ac S.rowAC S.cellAC hw (by omega)
    (by change src+bcN+abN+acN ≤ dst+4*(bcN+abN); omega)
    (by change dst+4*(bcN+abN)+4*acN ≤ lim.space; omega)
    hwordU hAU hCU hacBound hacRead
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcAC _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcAC ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBandCandidatesTable.time, _root_.ThreeSum.LightBandCandidatesRow.time, _root_.ThreeSum.LightBandCandidatesCell.time] <;> omega)
     on_goal -1 => (rintro unused ν₃ ⟨hac, hkeepAC⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hbc' : _root_.ThreeSum1960614.Machine.Light.Seg ν₃ dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect B.size C.size (_root_.ThreeSum.BandCandidateRows.bc A B C))) := by
    apply (hbc.of_sameOutside hkeepAB (Or.inl (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length]))).of_sameOutside
      hkeepAC (Or.inl (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length]; change dst+4*bcN ≤ dst+4*(bcN+abN); omega))
  have hab' : _root_.ThreeSum1960614.Machine.Light.Seg ν₃ (dst+4*bcN) (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect A.size B.size (_root_.ThreeSum.BandCandidateRows.ab A B C))) :=
    hab.of_sameOutside hkeepAC (Or.inl (by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length]
      change dst+4*bcN+4*abN ≤ dst+4*(bcN+abN)
      omega))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℕ) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,?_,?_⟩
  · rw [_root_.ThreeSum.BandCandidateRows.records,_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_append,List.flatMap_append]
    change _root_.ThreeSum1960614.Machine.Light.Seg ν₃ dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect B.size C.size (_root_.ThreeSum.BandCandidateRows.bc A B C)) ++
      (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect A.size B.size (_root_.ThreeSum.BandCandidateRows.ab A B C)) ++ _root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect A.size C.size (_root_.ThreeSum.BandCandidateRows.ac A B C))))
    apply platform_seg_append_f615a21baf.mpr
    refine ⟨hbc',?_⟩
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length]
    apply platform_seg_append_f615a21baf.mpr
    refine ⟨hab',?_⟩
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length]
    change _root_.ThreeSum1960614.Machine.Light.Seg ν₃ (dst+4*bcN+4*abN)
      (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect A.size C.size (fun i k => _root_.ThreeSum.BandCandidateRows.make _root_.ThreeSum.BandCandidateRows.Mode.ac i k
        (_root_.ThreeSum.LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)))))
    rw [show dst+4*bcN+4*abN=dst+4*(bcN+abN) by ring]
    exact hac
  · intro a ha
    change ν₃ a=μ a
    unfold _root_.Light.Outside at ha
    rw [hkeepAC a (by unfold _root_.Light.Outside; rw [hcount] at ha; omega),
      hkeepAB a (by unfold _root_.Light.Outside; rw [hcount] at ha; omega),
      hkeepBC a (by unfold _root_.Light.Outside; rw [hcount] at ha; omega)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets__implementation_a82d165fc8) := (@ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets__implementation_a82d165fc8)

#print axioms solution
