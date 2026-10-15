-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:34.091966+00:00
-- url     : https://prove2.me/submissions/db1a51de-3103-4697-b3ab-73183bf54c88

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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandTable_row_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBandTable
end ThreeSum.LightBandTable
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBandTable
end ThreeSum1960614.Machine.ThreeSum.LightBandTable
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











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





































theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl









































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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandTable
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets__implementation_cc563e84ac {pMain pRow pLookup pSearch a b loBase hiBase nX nY m dst powers W d U : ℕ}
    {s : ℤ} (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.body pRow))
    (hrow : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.rowBody pLookup))
    (hlookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f g lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nX ≤ dst) (hb : b+nY ≤ dst)
    (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+nX*nY ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hreadA : ∀ i < nX, μ (a+i) = f i)
    (hreadB : ∀ j < nY, μ (b+j) = g j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1)
    (hf : ∀ i < nX, |f i| ≤ U) (hg : ∀ j < nY, |g j| ≤ U)
    (hd : d+W+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s] μ (_root_.ThreeSum.LightBandTable.time nX nY W)
      (fun _ μ' =>
        (∀ i < nX, ∀ j < nY,
          μ' (dst+i*nY+j) = (_root_.ThreeSum.LightBandTable.rowValue lo hi m (f i) s g j : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (nX*nY)) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.body _root_.ThreeSum.LightBandTable.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for
    (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨_root_.Light.frame [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s,i,r],μ'⟩ ∧
      (∀ j < i, ∀ k < nY,
        μ' (dst+j*nY+k) = (_root_.ThreeSum.LightBandTable.rowValue lo hi m (f j) s g k : ℤ)) ∧
      _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (nX*nY))
    nX (_root_.ThreeSum.LightBandTable.rowTime nY W+62) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      simpa using (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s,0] 1).symm
    · intro j hj
      omega
  case round =>
    rintro i _ hin _ ⟨r,μ',rfl,written,kept⟩
    have hiMul : i*nY+nY ≤ nX*nY := by
      have hh := Nat.mul_le_mul_right nY (show i+1 ≤ nX by omega)
      simpa [Nat.add_mul] using hh
    have hiMulLe : i*nY ≤ nX*nY := by omega
    have hiMulNZ : (0 : ℤ) ≤ (i : ℤ)*(nY : ℤ) := by positivity
    have hiAddrWord : (dst : ℤ)+(i : ℤ)*(nY : ℤ) ≤ lim.word := by
      have hz : (dst : ℤ)+(i : ℤ)*(nY : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast (show dst+i*nY ≤ lim.space by omega)
      exact hz.trans hw
    have hrA : μ' (a+i) = f i :=
      (kept (a+i) (Or.inl (by omega))).trans (hreadA i hin)
    have hrB : ∀ j < nY, μ' (b+j) = g j := by
      intro j hj
      exact (kept (b+j) (Or.inl (by omega))).trans (hreadB j hj)
    have hrLo : ∀ j < m, μ' (loBase+j) = lo j := by
      intro j hj
      exact (kept (loBase+j) (Or.inl (by omega))).trans (hreadLo j hj)
    have hrHi : ∀ j < m, μ' (hiBase+j) = hi j := by
      intro j hj
      exact (kept (hiBase+j) (Or.inl (by omega))).trans (hreadHi j hj)
    have hpowers' : _root_.ThreeSum.LightSubsetAddress.Powers μ' powers W := by
      intro j hj
      rw [kept (powers+j) (Or.inr (by omega))]
      exact hpowers j hj
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.row_meets (d := d + 1) (x := f i) (s := s) (dst := dst + i * nY) hrow hlookup hsearch μ' g lo hi hw (by omega) (by omega) (by omega) (by omega) hspace hword hqueryWord hrB hrLo hrHi hpowers' hsorted hm hs (hf i hin) hg (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.row_meets (d := d + 1) (x := f i) (s := s) (dst := dst + i * nY) hrow hlookup hsearch μ' g lo hi hw (by omega) (by omega) (by omega) (by omega) hspace hword hqueryWord hrB hrLo hrHi hpowers' hsorted hm hs (hf i hin) hg (by omega)) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrA, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hrA, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, _root_.ThreeSum.LightBandTable.rowTime, _root_.ThreeSum.LightBandLookup.time, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
       on_goal -1 => (rintro returned μ'' ⟨rowWritten, rowKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,returned,μ'',by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · intro j hj k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hji : j*nY+nY ≤ i*nY := by
          have hh := Nat.mul_le_mul_right nY (show j+1 ≤ i by omega)
          simpa [Nat.add_mul] using hh
        rw [rowKept (dst+j*nY+k) (Or.inl (by omega))]
        exact written j hj k hk
      · exact rowWritten k hk
    · intro addr haddr
      rw [rowKept addr (by omega)]
      exact kept addr haddr
  case done =>
    rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,μ',rfl,written,kept⟩
    simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets__implementation_cc563e84ac) := (@ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets__implementation_cc563e84ac)

#print axioms solution
