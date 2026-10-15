-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:21.616875+00:00
-- url     : https://prove2.me/submissions/2f4ebb10-dbe1-4877-a3d7-b20d5972b495

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskErase_meets
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_le
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf

private theorem platform_seg_cons_31e338fb95 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_31e338fb95 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_31e338fb95 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase
open _root_.ThreeSum.MaskErase


open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress









theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.SubsetAddress.natPositions (s.erase a) = (_root_.ThreeSum.SubsetAddress.natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) = _root_.ThreeSum.SubsetAddress.subsetMask (s.erase a) := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.MaskErase.eraseMask_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s),
    ← _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.natPositions_erase, ← _root_.ThreeSum.SubsetAddress.subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) ≠ _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, (_root_.ThreeSum.SubsetAddress.subsetMask_injective L).ne_iff, Finset.erase_ne_self]

theorem eraseMask_lt_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) < _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  have hb := _root_.ThreeSum.MaskErase.eraseMask_le (a := a.val) (_root_.ThreeSum.SubsetAddress.subsetMask_isMask s).1
  rw [lt_iff_le_and_ne]
  simpa only [hb, true_and] using _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff s a



end ThreeSum.MaskErase

end ThreeSum1960614.Machine

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
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (x : ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  platform_seg_append_31e338fb95.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [platform_seg_cons_31e338fb95]⟩





















/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) (x : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [_root_.ThreeSum1960614.Machine.Light.SegN] using _root_.ThreeSum1960614.Machine.Light.Seg.snoc h (x : ℤ)























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
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.Light.powList 2 (W+1))) : _root_.ThreeSum.LightSubsetAddress.Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hs













end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators



@[simp] theorem positions_zero {W : ℕ} (Q : Finset (Fin W)) : _root_.ThreeSum.QueryCoordinates.positions Q 0 = [] := by
  simp [_root_.ThreeSum.QueryCoordinates.positions]

theorem positions_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    _root_.ThreeSum.QueryCoordinates.positions Q (j+1) = _root_.ThreeSum.QueryCoordinates.positions Q j ++ if j ∈ _root_.ThreeSum.SubsetAddress.natPositions Q then [j] else [] := by
  by_cases h : j ∈ _root_.ThreeSum.SubsetAddress.natPositions Q <;> simp [_root_.ThreeSum.QueryCoordinates.positions,List.range_succ,List.filter_append,h]





theorem positions_length_le {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.positions Q j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range



@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



@[simp] theorem selectedPowers_length {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.selectedPowers Q j).length = (_root_.ThreeSum.QueryCoordinates.positions Q j).length := by simp [_root_.ThreeSum.QueryCoordinates.selectedPowers]

@[simp] theorem selectedPowers_zero {W : ℕ} (Q : Finset (Fin W)) :
    _root_.ThreeSum.QueryCoordinates.selectedPowers Q 0 = [] := by simp [_root_.ThreeSum.QueryCoordinates.selectedPowers]

theorem selectedPowers_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    _root_.ThreeSum.QueryCoordinates.selectedPowers Q (j+1) =
      _root_.ThreeSum.QueryCoordinates.selectedPowers Q j ++ if j ∈ _root_.ThreeSum.SubsetAddress.natPositions Q then [2^j] else [] := by
  rw [_root_.ThreeSum.QueryCoordinates.selectedPowers,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_succ,List.map_append]
  split <;> simp [_root_.ThreeSum.QueryCoordinates.selectedPowers]







































end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightQueryWeights
open _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.meets__implementation_3e4178327e {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body pPowers pErase))
    (hPowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,_root_.ThreeSum.SubsetAddress.subsetMask Q,dst,work] μ (_root_.ThreeSum.LightQueryWeights.time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.QueryCoordinates.selectedPowers Q W) ∧ _root_.ThreeSum.LightSubsetAddress.Powers μ' work W ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst W) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body _root_.ThreeSum.LightQueryWeights.time
  have hp := _root_.ThreeSum1960614.Machine.Light.powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := W+1) (b := 2) hPowers hw hspace (by
      intro i hi
      have hh : (2^i : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hi
      exact (by exact_mod_cast hh : ((2^i : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time] <;> omega)
     on_goal -1 => (rintro powRet μ₁ ⟨hpow, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hpowers := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.powers_of_segment hpow
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime, _root_.ThreeSum.LightMaskErase.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for
    (T := W*(_root_.ThreeSum.LightMaskErase.time W+80)+20)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.Inv μ Q dst work powRet W)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.Inv μ Q dst work powRet) W (_root_.ThreeSum.LightMaskErase.time W+60)
    ?start ?round ?done ?bound (hT := by (first
                                          | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                              first
                                              | omega
                                              | (ring_nf; omega))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | (ring_nf; omega))))) ?after
  case start =>
    refine ⟨0,μ₁,?_,by simp [_root_.ThreeSum1960614.Machine.Light.SegN],hpowers,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(W : ℤ),_root_.ThreeSum.SubsetAddress.subsetMask Q,dst,work,powRet,0,0] =
        _root_.Light.frame ([(W : ℤ),_root_.ThreeSum.SubsetAddress.subsetMask Q,dst,work,powRet,0,0] ++ [0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm
    · intro i hi
      exact hkept i (Or.inl hi.1)
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    have hcBound := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length_le Q j
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.meets hErase μ' hw hspace hword hpowers'
      W j (_root_.ThreeSum.SubsetAddress.subsetMask Q) le_rfl (Nat.le_of_lt hj) (_root_.ThreeSum.SubsetAddress.subsetMask_isMask Q).1
      (d+1) (by omega)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.roundBody
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskErase.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightMaskErase.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskErase.time] <;> omega)
       on_goal -1 => (rintro erased μ₂ ⟨herased, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₂
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((_root_.ThreeSum.MaskErase.eraseMask W j (_root_.ThreeSum.SubsetAddress.subsetMask Q) : ℤ) < (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)) (fun hbit => ?_) (fun hnbit => ?_) ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, herased, _root_.ThreeSum.LightMaskErase.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [herased, _root_.ThreeSum.LightMaskErase.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, herased, _root_.ThreeSum.LightMaskErase.time] <;> omega)
       all_goals
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
    · have ha : (⟨j,hj⟩ : Fin W) ∈ Q :=
        (_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_lt_iff Q ⟨j,hj⟩).mp (by exact_mod_cast hbit)
      have hnat : j ∈ _root_.ThreeSum.SubsetAddress.natPositions Q := Finset.mem_map.mpr ⟨⟨j,hj⟩,ha,rfl⟩
      have hnext := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.selectedPowers_succ Q j
      rw [if_pos hnat] at hnext
      have hlen : (_root_.ThreeSum.QueryCoordinates.positions Q (j+1)).length = (_root_.ThreeSum.QueryCoordinates.positions Q j).length+1 := by
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_succ,if_pos hnat]
        simp
      have hread := hpowers' j (Nat.le_of_lt hj)
      have hvalWord : ((2^j : ℕ) : ℤ) ≤ lim.word := by
        have hh : (2^j : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact (by exact_mod_cast hh : ((2^j : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + (_root_.ThreeSum.QueryCoordinates.positions Q j).length) (2 ^ j : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskErase.time, hread]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightMaskErase.time, hread] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskErase.time, hread] <;> omega)
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
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((_root_.ThreeSum.QueryCoordinates.positions Q j).length + 1 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskErase.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightMaskErase.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskErase.time] <;> omega)
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      refine ⟨by simp,erased,
        Function.update μ' (dst+(_root_.ThreeSum.QueryCoordinates.positions Q j).length) ((2^j : ℕ) : ℤ),?_,?_,?_,?_⟩
      · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,hlen]
      · rw [hnext]
        simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.selectedPowers_length] using _root_.ThreeSum1960614.Machine.Light.SegN.snoc hseg (2^j)
      · intro i hi
        change Function.update μ' (dst+(_root_.ThreeSum.QueryCoordinates.positions Q j).length) ((2^j : ℕ) : ℤ) (work+i) = _
        rw [Function.update_of_ne (by omega)]
        exact hpowers' i hi
      · intro i hi
        change Function.update μ' (dst+(_root_.ThreeSum.QueryCoordinates.positions Q j).length) ((2^j : ℕ) : ℤ) i = _
        rw [Function.update_of_ne (by omega)]
        exact hkeep i hi
    · have ha : (⟨j,hj⟩ : Fin W) ∉ Q := by
        intro hh
        exact hnbit (by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_lt_iff Q ⟨j,hj⟩).mpr hh)
      have hnat : j ∉ _root_.ThreeSum.SubsetAddress.natPositions Q := by
        intro hh
        obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp hh
        exact ha ((Fin.ext hij : i = ⟨j,hj⟩) ▸ hi)
      have hpos : _root_.ThreeSum.QueryCoordinates.positions Q (j+1) = _root_.ThreeSum.QueryCoordinates.positions Q j := by
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_succ,if_neg hnat,List.append_nil]
      have hnext : _root_.ThreeSum.QueryCoordinates.selectedPowers Q (j+1) = _root_.ThreeSum.QueryCoordinates.selectedPowers Q j := by
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.selectedPowers_succ,if_neg hnat,List.append_nil]
      apply _root_.ThreeSum1960614.Machine.Light.Ends.skip
      refine ⟨by simp,erased,μ',?_,?_,hpowers',hkeep⟩
      · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,hpos]
      · rwa [hnext]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length_le Q W
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (Q.card : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp,hseg,hpowers',hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.meets__implementation_3e4178327e) := (@ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.meets__implementation_3e4178327e)

#print axioms solution
