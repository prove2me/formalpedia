-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:41:41.1824+00:00
-- url     : https://prove2.me/submissions/f1acf09d-6ac2-4c66-9400-88574a230bd7

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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightReportingPackKeys
end ThreeSum.LightReportingPackKeys
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys
end ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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













/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : _root_.Light.wrote μ dst f j (dst + i) = f i := by
  unfold _root_.Light.wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : _root_.Light.Outside dst j a) : _root_.Light.wrote μ dst f j a = μ a := by
  unfold _root_.Light.wrote
  rw [if_neg (by omega)]







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
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray
open _root_.ThreeSum.LightArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : _root_.ThreeSum.LightArray.SourceSafe src dst n) (hj : j < n) :
    _root_.Light.wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)











end ThreeSum.LightArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum.ReportingHostPackedCatalog


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder

set_option maxHeartbeats 600000









theorem pairKey_lt {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix left right < radix^2 := by unfold _root_.ThreeSum.ReportingHostPackedCatalog.pairKey; nlinarith



theorem packed_lt {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    _root_.ThreeSum.ReportingHostPackedCatalog.packed key n i < U*(n+1) := by unfold _root_.ThreeSum.ReportingHostPackedCatalog.packed; nlinarith



















end ThreeSum.ReportingHostPackedCatalog

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingPackKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.meets__implementation_50afe289c7 {p inL inR n radix dst : ℕ} {μ : ℕ → ℤ}
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.body) (left right : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hleft : inL+n ≤ dst) (hright : inR+n ≤ dst) (hdst : dst+n ≤ lim.space)
    (hword : (_root_.ThreeSum.LightReportingPackKeys.word radix n : ℤ) ≤ lim.word)
    (hreadL : ∀ i < n, μ (inL+i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (right i : ℤ))
    (hboundL : ∀ i < n, left i < radix) (hboundR : ∀ i < n, right i < radix) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [inL,inR,n,radix,dst] μ (_root_.ThreeSum.LightReportingPackKeys.time n)
      (fun _ μ' => _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum.ReportingHostPackedCatalog.codes (fun i => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left i) (right i)) n) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by
  have hnWord : ((n+1 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightReportingPackKeys.word; omega : n+1 ≤ word radix n)).trans hword
  have hsepL : _root_.ThreeSum.LightArray.SourceSafe inL dst n := Or.inr (Or.inl hleft)
  have hsepR : _root_.ThreeSum.LightArray.SourceSafe inR dst n := Or.inr (Or.inl hright)
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass
    (fun i => (_root_.ThreeSum.ReportingHostPackedCatalog.packed (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) n i : ℤ))
    (fun i hi => ?_) ⟨?_,by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
                               intro p2m_macro_12545772195636606797 p2m_macro_4265689903731703288
                               first
                               | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_4322064052873904471); (try have := p2m_macro_4322064052873904471 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_4322064052873904471)
                                     intros
                                     try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                               |
                                 (simp [] at p2m_macro_4265689903731703288;
                                   ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_11945687192546809425); (try have := p2m_macro_11945687192546809425 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_11945687192546809425)
                                     intros
                                     try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                               | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_17476295892461720639); (try have := p2m_macro_17476295892461720639 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_17476295892461720639)
                                     intros
                                     try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                                   fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                               its condition K x does not follow from the hypotheses.")))⟩ hw hdst rfl rfl (hT := by (first
                                                                   | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPackKeys.time]
                                                                       first
                                                                       | omega
                                                                       | (ring_nf; omega))
                                                                   | omega
                                                                   |
                                                                     (simp [_root_.ThreeSum.LightReportingPackKeys.time] <;>
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega)))))
  · have hrL := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.source_read (μ := μ)
      (f := fun i => (_root_.ThreeSum.ReportingHostPackedCatalog.packed (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) n i : ℤ)) hsepL hi
    have hrR := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.source_read (μ := μ)
      (f := fun i => (_root_.ThreeSum.ReportingHostPackedCatalog.packed (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) n i : ℤ)) hsepR hi
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.pairKey_lt (hboundL i hi) (hboundR i hi)
    have hf := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.packed_lt (key := fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) hi hb
    simp only [_root_.ThreeSum.ReportingHostPackedCatalog.packed,_root_.ThreeSum.ReportingHostPackedCatalog.pairKey,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hrL hrR
    have hmN : radix*right i ≤ _root_.ThreeSum.LightReportingPackKeys.word radix n := by unfold _root_.ThreeSum.ReportingHostPackedCatalog.pairKey at hb; unfold _root_.ThreeSum.LightReportingPackKeys.word; nlinarith
    have hkN : _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left i) (right i) ≤ _root_.ThreeSum.LightReportingPackKeys.word radix n := by unfold _root_.ThreeSum.LightReportingPackKeys.word; nlinarith
    have hpN : _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left i) (right i)*(n+1) ≤ _root_.ThreeSum.LightReportingPackKeys.word radix n := by
      simp only [_root_.ThreeSum.ReportingHostPackedCatalog.packed] at hf
      unfold _root_.ThreeSum.LightReportingPackKeys.word
      omega
    have hfN : _root_.ThreeSum.ReportingHostPackedCatalog.packed (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) n i ≤ _root_.ThreeSum.LightReportingPackKeys.word radix n := by
      unfold _root_.ThreeSum.LightReportingPackKeys.word
      omega
    have hmZ : (radix : ℤ)*(right i : ℤ) ≤ lim.word := (by exact_mod_cast hmN :
      (radix : ℤ)*(right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hkZ : (left i : ℤ)+(radix : ℤ)*(right i : ℤ) ≤ lim.word := (by exact_mod_cast hkN :
      (left i : ℤ)+(radix : ℤ)*(right i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hpZ : ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ lim.word :=
      (by exact_mod_cast hpN :
        ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ (word radix n : ℤ)).trans hword
    have hfZ : ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(i : ℤ) ≤ lim.word :=
      (by exact_mod_cast hfN :
        ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(i : ℤ) ≤ (word radix n : ℤ)).trans hword
    have hm0 : 0 ≤ (radix : ℤ)*(right i : ℤ) := by positivity
    have hp0 : 0 ≤ ((left i : ℤ)+(radix : ℤ)*(right i : ℤ))*((n : ℤ)+1) := by positivity
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrL, hrR, hreadL i hi, hreadR i hi, _root_.ThreeSum.ReportingHostPackedCatalog.packed, _root_.ThreeSum.ReportingHostPackedCatalog.pairKey] <;> omega))
  · intro i hi
    have hi' : i < n := by simpa only [_root_.ThreeSum.ReportingHostPackedCatalog.codes,List.length_ofFn] using hi
    simpa only [_root_.ThreeSum.ReportingHostPackedCatalog.codes,List.getElem_ofFn] using
      (_root_.ThreeSum1960614.Machine.Light.wrote_done (μ := μ) (dst := dst)
        (f := fun i => (_root_.ThreeSum.ReportingHostPackedCatalog.packed (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix (left j) (right j)) n i : ℤ)) hi')
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.meets__implementation_50afe289c7) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPackKeys.meets__implementation_50afe289c7)

#print axioms solution
