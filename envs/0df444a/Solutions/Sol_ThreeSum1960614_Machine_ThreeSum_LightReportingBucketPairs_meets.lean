-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:21.199428+00:00
-- url     : https://prove2.me/submissions/e287d0d2-a83d-4dd5-b88d-820c7cf3ab29

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketRow_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingBucketPairs
end ThreeSum.LightReportingBucketPairs
namespace ThreeSum.LightReportingBucketRow
end ThreeSum.LightReportingBucketRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow

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
# Exact original-value testing of one retained physical bucket

The procedure visits the bucket's physical index array and reads the original
value at each index. It counts exact integer equalities with the supplied
target and preserves every memory cell. Equal values at distinct original
indices remain separate tests.
-/

namespace ThreeSum.LightReportingBucketRow
open _root_.ThreeSum.LightReportingBucketRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



@[simp] theorem count_zero (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) :
    _root_.ThreeSum.LightReportingBucketRow.count target value index 0 = 0 := by simp [_root_.ThreeSum.LightReportingBucketRow.count]

theorem count_le (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.LightReportingBucketRow.count target value index n ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)












variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-value testing of a retained Cartesian bucket pair

Every pair of retained physical indices is tested using the original integer
arrays. The result counts exactly the pairs with `a+b=c`. An empty right
fiber skips the entire left scan, so the verified cost is linear in the
actual Cartesian pair mass plus one, including empty fibers.
-/

namespace ThreeSum.LightReportingBucketPairs
open _root_.ThreeSum.LightReportingBucketPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



@[simp] theorem count_zero (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR : ℕ) :
    _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR 0 = 0 := by simp [_root_.ThreeSum.LightReportingBucketPairs.count]

@[simp] theorem count_right_zero (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nL : ℕ) :
    _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR 0 nL = 0 := by simp [_root_.ThreeSum.LightReportingBucketPairs.count]

theorem count_succ (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR (nL+1) = _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL+
      _root_.ThreeSum.LightReportingBucketRow.count (a+left (indexL nL)) right indexR nR :=
  Finset.sum_range_succ _ _

theorem count_le (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL ≤ nL*nR := by
  unfold _root_.ThreeSum.LightReportingBucketPairs.count
  calc
    _ ≤ ∑ _i ∈ range nL, nR :=
      Finset.sum_le_sum (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.count_le _ _ _ _)
    _ = _ := by simp












variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketPairs

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBucketPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets__implementation_74bc09e66d {pMain pRow srcL srcR indicesL indicesR nL nR NL NR : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.body pRow)) (hrow : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrcL : srcL+NL ≤ lim.space) (hsrcR : srcR+NR ≤ lim.space)
    (hindicesL : indicesL+nL ≤ lim.space) (hindicesR : indicesR+nR ≤ lim.space)
    (hindexL : ∀ i < nL, indexL i < NL) (hindexR : ∀ j < nR, indexR j < NR)
    (hreadIL : ∀ i < nL, μ (indicesL+i) = (indexL i : ℤ))
    (hreadIR : ∀ j < nR, μ (indicesR+j) = (indexR j : ℤ))
    (hreadL : ∀ i < NL, μ (srcL+i) = left i) (hreadR : ∀ j < NR, μ (srcR+j) = right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ lim.word) (hvaluesR : ∀ j < NR, |right j| ≤ lim.word)
    (ha : |a| ≤ lim.word) (htarget : ∀ i < NL, |a+left i| ≤ lim.word)
    (hcountWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,srcL,srcR,indicesL,indicesR,nL,nR,NL,NR] μ (_root_.ThreeSum.LightReportingBucketPairs.time nL nR)
      (fun r ν => r=(_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL : ℤ) ∧ ν=μ) := by
  have haBounds := abs_le.mp ha
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.body _root_.ThreeSum.LightReportingBucketPairs.time
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
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < (nR : ℤ)) (fun hrposZ => ?_) (fun hrzeroZ => ?_) ?_ ?_
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
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have hrpos : 0<nR := by exact_mod_cast hrposZ
    have hnLcost : nL ≤ nL*nR := Nat.le_mul_of_pos_right _ hrpos
    refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (lim := lim) (P := P) (d := d) (i := 10) (hi := _root_.ThreeSum1960614.Machine.Light.v 5)
      (body := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.roundBody pRow) (T := nL*(_root_.ThreeSum.LightReportingBucketRow.time nR+100)+30)
      (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.Inv μ a left right indexL indexR srcL srcR indicesL indicesR nL nR NL NR nL)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.Inv μ a left right indexL indexR srcL srcR indicesL indicesR nL nR NL NR)
      nL (_root_.ThreeSum.LightReportingBucketRow.time nR+80) ?start ?round ?done ?bound
      (hT := by (first
                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketRow.time]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [_root_.ThreeSum.LightReportingBucketRow.time] <;>
                       first
                       | omega
                       | (ring_nf; omega))))) ?after
      (hT := by (first
                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketRow.time]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [_root_.ThreeSum.LightReportingBucketRow.time] <;>
                       first
                       | omega
                       | (ring_nf; omega))))
    case start =>
      refine ⟨0,0,0,?_⟩
      simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 3).symm
    case round =>
      rintro i _ hi _ ⟨oldLeft,oldTarget,oldRet,rfl⟩
      have hii := hindexL i hi
      have hreadIdx := hreadIL i hi
      have hreadVal := hreadL _ hii
      have hv := abs_le.mp (hvaluesL _ hii)
      have ht := abs_le.mp (htarget _ hii)
      have htotal := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.count_le a left right indexL indexR nR (i+1)
      have hmul := Nat.mul_le_mul_right nR (show i+1 ≤ nL by omega)
      have hnextWord : (_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR (i+1) : ℤ) ≤ lim.word :=
        (Int.ofNat_le.mpr (htotal.trans hmul)).trans hcountWord
      have hnext := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.count_succ a left right indexL indexR nR i
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.roundBody
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (left (indexL i)) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadIdx, hreadVal, _root_.ThreeSum.LightReportingBucketRow.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hreadIdx, hreadVal, _root_.ThreeSum.LightReportingBucketRow.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadIdx, hreadVal, _root_.ThreeSum.LightReportingBucketRow.time] <;> omega)
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
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (a + left (indexL i)) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketRow.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightReportingBucketRow.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketRow.time] <;> omega)
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
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.meets (d := d + 1) hrow (a + left (indexL i)) right indexR hw hsrcR hindicesR hindexR hreadIR hreadR hvaluesR (htarget _ hii)) _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.meets (d := d + 1) hrow (a + left (indexL i)) right indexR hw hsrcR hindicesR hindexR hreadIR hreadR hvaluesR (htarget _ hii)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketRow.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightReportingBucketRow.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 => omega
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketRow.time] <;> omega)
         on_goal -1 => (rintro found ν ⟨hfound, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
      subst ν
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR (i + 1) : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, hnext, _root_.ThreeSum.LightReportingBucketRow.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hfound, hnext, _root_.ThreeSum.LightReportingBucketRow.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, hnext, _root_.ThreeSum.LightReportingBucketRow.time] <;> omega)
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      exact ⟨by simp,left (indexL i),a+left (indexL i),found,by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]⟩
    case done => intro σ _ hs; exact hs
    case bound => rintro i _ hi _ ⟨oldLeft,oldTarget,oldRet,rfl⟩; (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    case after =>
      rintro _ ⟨oldLeft,oldTarget,oldRet,rfl⟩
      have hc : (_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL : ℤ) ≤ lim.word :=
        (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.count_le _ _ _ _ _ _ _)).trans hcountWord
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketRow.time]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightReportingBucketRow.time] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketRow.time] <;> omega)
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      exact ⟨rfl,rfl⟩
  · have hrzero : nR=0 := by omega
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
    simp [hrzero]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets__implementation_74bc09e66d) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets__implementation_74bc09e66d)

#print axioms solution
