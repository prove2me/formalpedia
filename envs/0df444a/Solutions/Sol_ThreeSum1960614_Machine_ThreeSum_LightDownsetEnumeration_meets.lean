-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:26.324747+00:00
-- url     : https://prove2.me/submissions/319b992b-2d14-48b8-acbe-ff10d6615136

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumeration_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

private theorem platform_seg_append_b31fe96c14 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_b31fe96c14 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightDownsetEnumeration
end ThreeSum.LightDownsetEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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















































@[simp] theorem layerOffset_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L 0 = 0 := by
  simp [_root_.ThreeSum.SubsetAddress.layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega







































































end ThreeSum.SubsetAddress

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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl





/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : _root_.ThreeSum1960614.Machine.Light.SameOn K₁ μ μ') (h₂ : _root_.ThreeSum1960614.Machine.Light.SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)



/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]











theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl









/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)















/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.SegN μ' b l :=
  _root_.ThreeSum1960614.Machine.Light.Seg.of_sameOutside h hs (by simpa using hd)















end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration
open _root_.ThreeSum.LightSubsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (L k : ℕ) :
    _root_.ThreeSum.LightSubsetEnumeration.time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (_root_.ThreeSum.SubsetAddress.enumerationWork_bound L k)







end ThreeSum.LightSubsetEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Sequential enumeration of a compact downset

This routine invokes the guarded layer enumerator for the successive
cardinalities. Each layer starts immediately after the preceding layer;
the only traversal besides the emitted masks is polynomial in the bit
width. All power-table reads are shared across the layer calls.
-/

namespace ThreeSum.LightDownsetEnumeration
open _root_.ThreeSum.LightDownsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem layers_length (L j : ℕ) : (_root_.ThreeSum.LightDownsetEnumeration.layers L j).length = _root_.ThreeSum.SubsetAddress.layerOffset L j := by
  induction j with
  | zero => simp [_root_.ThreeSum.LightDownsetEnumeration.layers]
  | succ j ih =>
    simp only [_root_.ThreeSum.LightDownsetEnumeration.layers,List.length_append,ih,_root_.ThreeSum.SubsetAddress.enumerateLayer_length,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]

theorem layers_eq_through (L j : ℕ) : _root_.ThreeSum.LightDownsetEnumeration.layers L (j+1) = _root_.ThreeSum.SubsetAddress.enumerateThrough L j := by
  induction j with
  | zero => simp [_root_.ThreeSum.LightDownsetEnumeration.layers,_root_.ThreeSum.SubsetAddress.enumerateThrough]
  | succ j ih =>
    change _root_.ThreeSum.LightDownsetEnumeration.layers L (j+1) ++ _root_.ThreeSum.SubsetAddress.enumerateLayer L (j+1) = _
    rw [ih]
    rfl

theorem layers_eq_downset {L cut : ℕ} (hcut : cut ≤ L) :
    _root_.ThreeSum.LightDownsetEnumeration.layers L (cut+1) = _root_.ThreeSum.SubsetAddress.enumerateDownset L cut := by
  simp only [_root_.ThreeSum.SubsetAddress.enumerateDownset,Nat.min_eq_left hcut,_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.layers_eq_through]



theorem layer_time_le_budget {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    _root_.ThreeSum.LightSubsetEnumeration.time L j ≤ _root_.ThreeSum.LightDownsetEnumeration.budget L cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (show j+1 ≤ cut+1 by omega)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ] at ho
  have hcap : _root_.ThreeSum.SubsetAddress.layerOffset L (cut+1) = _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
    simp [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut]
  have hc : L.choose j ≤ _root_.ThreeSum.SubsetAddress.downsetCap L cut := by omega
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound L j
  exact h.trans (Nat.mul_le_mul_left 150
    (Nat.add_le_add_right (Nat.mul_le_mul_left (4*L+1) hc) 1))

















end ThreeSum.LightDownsetEnumeration

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightDownsetEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets__implementation_92f58b66f8 {pMain pEnum L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.body pEnum))
    (henum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ powers)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,dst,powers] μ (_root_.ThreeSum.LightDownsetEnumeration.time L cut)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by
  have hcap : _root_.ThreeSum.SubsetAddress.layerOffset L (cut+1) = _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
    simp [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.body _root_.ThreeSum.LightDownsetEnumeration.time
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumeration.budget]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetEnumeration.budget] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumeration.budget] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for
    (T := (cut+1)*(_root_.ThreeSum.LightDownsetEnumeration.budget L cut+70)+20)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.Inv μ L cut dst powers (cut+1))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.Inv μ L cut dst powers) (cut+1) (_root_.ThreeSum.LightDownsetEnumeration.budget L cut+50)
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
    refine ⟨0,μ,?_,?_,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_zero]
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(L : ℤ),cut,dst,powers,0,0] 1).symm
    · exact _root_.ThreeSum1960614.Machine.Light.Seg.nil
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hsame⟩
    have hjcut : j ≤ cut := by omega
    have hpart := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (show j+1 ≤ cut+1 by omega)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ,hcap] at hpart
    have hpartial : dst+_root_.ThreeSum.SubsetAddress.layerOffset L j ≤ powers := by omega
    have hnext : dst+_root_.ThreeSum.SubsetAddress.layerOffset L j+L.choose j ≤ powers := by omega
    have hpowers' : _root_.ThreeSum.LightSubsetAddress.Powers μ' powers L := by
      intro i hi
      rw [hsame (powers+i) (Or.inr (by omega))]
      exact hpowers i hi
    have hcall := (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.meets henum hw hspace hword
      L j 0 (dst+_root_.ThreeSum.SubsetAddress.layerOffset L j) μ' le_rfl (by omega) (by simp) hnext hpowers'
      (d+1) (by omega)).mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.layer_time_le_budget hcut hjcut)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.roundBody
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumeration.budget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightDownsetEnumeration.budget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumeration.budget] <;> omega)
       on_goal -1 => (rintro n μ₁ ⟨hn, hnew, hsame₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hnewN : _root_.ThreeSum1960614.Machine.Light.SegN μ₁ (dst+_root_.ThreeSum.SubsetAddress.layerOffset L j) (_root_.ThreeSum.SubsetAddress.enumerateLayer L j) := by
      simpa [_root_.ThreeSum.LightSubsetEnumeration.output] using hnew
    have hseg' : _root_.ThreeSum1960614.Machine.Light.SegN μ₁ dst (_root_.ThreeSum.LightDownsetEnumeration.layers L j) :=
      hseg.of_sameOutside hsame₁ (Or.inl (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.layers_length]))
    have hsum : _root_.ThreeSum.SubsetAddress.layerOffset L j+L.choose j ≤ lim.space := by omega
    have hsumZ : (_root_.ThreeSum.SubsetAddress.layerOffset L j : ℤ)+(L.choose j : ℤ) ≤ lim.word := by
      have hb : (_root_.ThreeSum.SubsetAddress.layerOffset L j : ℤ)+(L.choose j : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast hsum
      exact hb.trans hw
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.layerOffset L (j + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hn, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ, _root_.ThreeSum.LightDownsetEnumeration.budget]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hn, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ, _root_.ThreeSum.LightDownsetEnumeration.budget] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hn, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ, _root_.ThreeSum.LightDownsetEnumeration.budget] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,n,μ₁,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · change _root_.ThreeSum1960614.Machine.Light.Seg μ₁ dst (((_root_.ThreeSum.LightDownsetEnumeration.layers L j) ++ _root_.ThreeSum.SubsetAddress.enumerateLayer L j).map _)
      rw [List.map_append,platform_seg_append_b31fe96c14,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.layers_length]
      exact ⟨hseg',hnewN⟩
    · exact hsame.then hsame₁ (fun a ha => by
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ] at ha
        constructor <;> omega)
  case done =>
    intro σ _ hI
    exact hI
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨r,μ',rfl,hseg,hsame⟩
    have hcZ : (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ≤ lim.word := by
      have hb : (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast (show _root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ lim.space by omega)
      exact hb.trans hw
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcap] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp, by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.layers_eq_downset hcut] using hseg,
      by simpa only [hcap] using hsame⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets__implementation_92f58b66f8) := (@ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets__implementation_92f58b66f8)

#print axioms solution
