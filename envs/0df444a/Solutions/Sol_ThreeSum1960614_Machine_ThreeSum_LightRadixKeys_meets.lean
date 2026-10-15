-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:52.01602+00:00
-- url     : https://prove2.me/submissions/7e50003d-e08f-4b61-a38a-68326a6743ed

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixRows_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_bounded

private theorem platform_seg_cons_7517fb12c9 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

@[simp] private theorem platform_seg_nil_7517fb12c9 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightRadixKeys
end ThreeSum.LightRadixKeys
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
end ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists
open _root_.ThreeSum.RadixKeyLists


variable {α β : Type*}





theorem step_length (p : ℤ) (base prev : List ℤ) :
    (_root_.ThreeSum.RadixKeyLists.step p base prev).length=base.length*prev.length :=
  _root_.ThreeSum.RadixKeyLists.flatMap_length_uniform base _ prev.length (by simp)





theorem values_length (p : ℤ) (base : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.RadixKeyLists.values p base j).length=base.length^j := by
  induction j with
  | zero => simp [_root_.ThreeSum.RadixKeyLists.values]
  | succ j ih => rw [_root_.ThreeSum.RadixKeyLists.values,_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.step_length,ih,pow_succ']













end ThreeSum.RadixKeyLists

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





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _















































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
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys
open _root_.ThreeSum.LightRadixKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000



theorem le_offset (m j : ℕ) : j ≤ _root_.ThreeSum.LightRadixKeys.offset m j := by
  induction j with
  | zero => simp [_root_.ThreeSum.LightRadixKeys.offset]
  | succ j ih => rw [_root_.ThreeSum.LightRadixKeys.offset]; omega






theorem space_step (dst m j : ℕ) : _root_.ThreeSum.LightRadixKeys.space dst m j ≤ _root_.ThreeSum.LightRadixKeys.space dst m (j+1) := by
  unfold _root_.ThreeSum.LightRadixKeys.space
  rw [_root_.ThreeSum.LightRadixKeys.offset]
  omega

theorem word_mono {p U j k : ℕ} (hj : j ≤ k) : _root_.ThreeSum.LightRadixKeys.word p U j ≤ _root_.ThreeSum.LightRadixKeys.word p U k := by
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ p+1) hj
  have hv := Nat.mul_le_mul_left U hpow
  have hpv := Nat.mul_le_mul_left p hv
  unfold _root_.ThreeSum.LightRadixKeys.word _root_.ThreeSum.LightRadixRows.word
  omega







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightRadixKeys

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightRadixKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets__implementation_8a67650a8a {pMain pRows pAffine src dst p U : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body pMain pRows))
    (hrows : P[pRows]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body pAffine))
    (haffine : P[pAffine]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body)
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ)) :
    ∀ J d : ℕ, ∀ μ : ℕ → ℤ,
      _root_.ThreeSum.LightRadixKeys.space dst base.length J ≤ lim.space → (_root_.ThreeSum.LightRadixKeys.word p U J : ℤ) ≤ lim.word →
      d+J+2 ≤ lim.depth → _root_.ThreeSum1960614.Machine.Light.Seg μ src base →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,base.length,J,p,dst] μ (_root_.ThreeSum.LightRadixKeys.time base.length J)
        (fun r ν => r = ((dst+_root_.ThreeSum.LightRadixKeys.offset base.length J : ℕ) : ℤ) ∧
          ν (dst+_root_.ThreeSum.LightRadixKeys.offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+_root_.ThreeSum.LightRadixKeys.offset base.length J+1) (_root_.ThreeSum.RadixKeyLists.values (p : ℤ) base J) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  intro J
  induction J with
  | zero =>
    intro d μ hspace hword hd hread
    have hs : dst+2 ≤ lim.space := by
      simp only [_root_.ThreeSum.LightRadixKeys.space,_root_.ThreeSum.LightRadixKeys.offset,pow_zero,Nat.add_zero] at hspace
      omega
    apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body _root_.ThreeSum.LightRadixKeys.time
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (1 : ℕ) ?_ ?_ ?_
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (0 : ℕ) ?_ ?_ ?_
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
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
    refine ⟨by simp [_root_.ThreeSum.LightRadixKeys.offset],?_,?_,?_⟩
    · simp [_root_.ThreeSum.LightRadixKeys.offset,Function.update_of_ne (by omega : dst ≠ dst+1)]
    · simp [_root_.ThreeSum.RadixKeyLists.values,_root_.ThreeSum.LightRadixKeys.offset,platform_seg_cons_7517fb12c9]
    · intro a ha
      simp only [_root_.ThreeSum1960614.Machine.Light.State.mem]
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  | succ J ih =>
    intro d μ hspace hword hd hread
    let old := dst+_root_.ThreeSum.LightRadixKeys.offset base.length J
    let next := old+1+base.length^J
    have hnext : next = dst+_root_.ThreeSum.LightRadixKeys.offset base.length (J+1) := by dsimp [next,old,_root_.ThreeSum.LightRadixKeys.offset]; omega
    have hs : next+1+base.length^(J+1) ≤ lim.space := by rw [hnext]; exact hspace
    have hJ : J+1 ≤ _root_.ThreeSum.LightRadixKeys.offset base.length (J+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.le_offset _ _
    have hn : 0 < base.length^J := Nat.pow_pos hm
    have hrowWord : (_root_.ThreeSum.LightRadixRows.word p U (U*(p+1)^J) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.word_mono (p := p) (U := U) (Nat.le_succ J))).trans hword
    have hpWord : (p : ℤ) ≤ lim.word := by
      exact (Int.ofNat_le.mpr (show p ≤ _root_.ThreeSum.LightRadixKeys.word p U (J+1) by
        unfold _root_.ThreeSum.LightRadixKeys.word _root_.ThreeSum.LightRadixRows.word; omega)).trans hword
    have hprod : (base.length : ℤ)*((base.length^J : ℕ) : ℤ) ≤ lim.word := by
      have hh : base.length*base.length^J ≤ lim.space := by rw [← pow_succ']; omega
      exact (by exact_mod_cast hh : (base.length : ℤ)*((base.length^J : ℕ) : ℤ) ≤ lim.space).trans hw
    apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body _root_.ThreeSum.LightRadixKeys.time
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((ih (d + 1) μ ((_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.space_step dst base.length J).trans hspace) hrowWord (by omega) hread) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ih (d + 1) μ ((_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.space_step dst base.length J).trans hspace) hrowWord (by omega) hread) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
       on_goal -1 => (rintro r ν₀ ⟨hresult, hheader, hprev, hkeep₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hr : r = (old : ℤ) := hresult
    have hh : ν₀ old = ((base.length^J : ℕ) : ℤ) := hheader
    have hpowerNonneg : (0 : ℤ) ≤ (base.length : ℤ)^J := by positivity
    have hprodInt : (base.length : ℤ)*(base.length : ℤ)^J ≤ lim.word := by
      simpa only [Nat.cast_pow] using hprod
    have hprodNonneg : (0 : ℤ) ≤ (base.length : ℤ)*(base.length : ℤ)^J := by positivity
    have hnextWord : (old : ℤ)+1+(base.length : ℤ)^J ≤ lim.word := by
      have hnat : next ≤ lim.space := by omega
      simpa only [next,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using
        (Int.ofNat_le.mpr hnat).trans hw
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (base.length ^ J : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, hh, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hr, hh, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hh, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (next : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, hh, next, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hr, hh, next, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, hh, next, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen next (base.length ^ (J + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, pow_succ', _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [pow_succ', _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_succ', _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    let ν₁ := Function.update ν₀ next ((base.length^(J+1) : ℕ) : ℤ)
    have hprev₁ : _root_.ThreeSum1960614.Machine.Light.Seg ν₁ (old+1) (_root_.ThreeSum.RadixKeyLists.values (p : ℤ) base J) := by
      apply hprev.update_out
      right
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length]
    have hbase₁ : _root_.ThreeSum1960614.Machine.Light.Seg ν₁ src base := by
      intro i hi
      change Function.update ν₀ next _ (src+i) = _
      rw [Function.update_of_ne (by dsimp [next,old]; omega),hkeep₀ _ (by omega)]
      exact hread i hi
    have hsRows : next+1+base.length*(_root_.ThreeSum.RadixKeyLists.values (p : ℤ) base J).length ≤ lim.space := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length,← pow_succ']
      exact hs
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.meets (d := d+1) (μ := ν₁) (srcBase := src)
      (srcPrev := old+1) (dst := next+1) (p := p) (U := U) (V := U*(p+1)^J)
      hrows haffine base (_root_.ThreeSum.RadixKeyLists.values (p : ℤ) base J) hw (by dsimp [next,old]; omega)
      (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length]; dsimp [next]; omega) hsRows hrowWord (by omega)
      hbase₁ hprev₁ hbound (_root_.ThreeSum.RadixKeyLists.values_bounded p U base hbound J)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length] at hc
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length, hr, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length, hr, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.values_length, hr, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
       on_goal -1 => (rintro result ν₂ ⟨hvalues, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (next : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightRadixRows.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp [hnext],?_,?_,?_⟩
    · change ν₂ (dst+_root_.ThreeSum.LightRadixKeys.offset base.length (J+1)) = _
      rw [← hnext,hkeep₁ _ (Or.inl (by omega))]
      exact Function.update_self ..
    · change _root_.ThreeSum1960614.Machine.Light.Seg ν₂ (dst+_root_.ThreeSum.LightRadixKeys.offset base.length (J+1)+1) _
      rw [← hnext]
      exact hvalues
    · intro a ha
      change ν₂ a = μ a
      rw [hkeep₁ _ (Or.inl (by dsimp [next,old]; omega))]
      change Function.update ν₀ next _ a = μ a
      rw [Function.update_of_ne (by dsimp [next,old]; omega)]
      exact hkeep₀ a ha
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets__implementation_8a67650a8a) := (@ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets__implementation_8a67650a8a)

#print axioms solution
