-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:34:35.139962+00:00
-- url     : https://prove2.me/submissions/e9f5525b-e8bd-4fb5-b8fe-088b3d088f35

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRowFlag_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceFlagTest
end ThreeSum.LightSourceFlagTest
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSourceTrim
end ThreeSum.LightSourceTrim
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
end ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

namespace ThreeSum1960614.Machine

/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct
open _root_.ThreeSum.SourceFlagProduct


open _root_.Finset
open scoped _root_.BigOperators



@[simp] theorem product_zero (flag : ℕ → ℕ) : _root_.ThreeSum.SourceFlagProduct.product flag 0=1 := by simp [_root_.ThreeSum.SourceFlagProduct.product]

theorem product_succ (flag : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.SourceFlagProduct.product flag (n+1)=_root_.ThreeSum.SourceFlagProduct.product flag n*flag n := Finset.prod_range_succ _ _

theorem product_le {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : _root_.ThreeSum.SourceFlagProduct.product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)





end ThreeSum.SourceFlagProduct

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

/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest
open _root_.ThreeSum.LightSourceFlagTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem flag_le (card required count cap : ℕ) : _root_.ThreeSum.LightSourceFlagTest.flag card required count cap ≤ 1 := by
  unfold _root_.ThreeSum.LightSourceFlagTest.flag
  split <;> omega







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightSourceFlagTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag
open _root_.ThreeSum.LightSourceRowFlag


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    _root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 hist ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.flag_le ..









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightSourceRowFlag

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim
open _root_.ThreeSum.LightSourceTrim


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem rowFlag_le (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    _root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.flag_le ..











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceTrim

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceTrim
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs.meets__implementation_932c38d4aa {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR bitBase rowOut work dst U V M K : ℕ}
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ rowOut) (hmaps : maps+2*L*M ≤ rowOut)
    (hcandidates : candidates+M ≤ rowOut)
    (hleft : histL+K*p ≤ rowOut) (hright : histR+K*p ≤ rowOut)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work) (hdst : dst+2 ≤ rowOut)
    (hspace : _root_.ThreeSum.LightSourceRowFlag.space work L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hbitsRead : ∀ i < J*L, μ (bitBase+i) = (bits i : ℤ))
    (hbitBound : ∀ i < J*L, bits i ≤ 1)
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst]
      μ (_root_.ThreeSum.LightSourceTrim.time J L U) (fun _ ν =>
        ν dst = (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν rowOut dst 2) := by
  have hspace' : work+3+(Nat.log 2 (L*U+1)+2) ≤ lim.space := hspace
  have h1 : (1 : ℤ) ≤ lim.word := by
    have hh : 1 ≤ _root_.ThreeSum.LightSourceRowFlag.word L p U V cap := by
      unfold _root_.ThreeSum.LightSourceRowFlag.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hleftFlag (j : ℕ) :
      _root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount j ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.rowFlag_le ..
  have hrightFlag (j : ℕ) :
      _root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount j ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.rowFlag_le ..
  have hleftPrefix (j : ℕ) :
      _root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) j ≤ 1 :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_le _ (n := j) (fun i _ => hleftFlag i) le_rfl
  have hrightPrefix (j : ℕ) :
      _root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) j ≤ 1 :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_le _ (n := j) (fun i _ => hrightFlag i) le_rfl
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.body _root_.ThreeSum.LightSourceTrim.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen 1 ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen 1 ?_ ?_ ?_
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
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst
      sel candidate bits w0 w1 leftCount rightCount) J (_root_.ThreeSum.LightSourceRowFlag.time L U+242)
    ?start ?round ?done ?bound
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Inv μ J L h p cap occ maps candidates histL histR bitBase rowOut work dst
      sel candidate bits w0 w1 leftCount rightCount J)
    (T := J*(_root_.ThreeSum.LightSourceRowFlag.time L U+250)+6) (hT := by (first
                                                                            | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                first
                                                                                | omega
                                                                                | (ring_nf; omega))
                                                                            | omega
                                                                            |
                                                                              (simp [] <;>
                                                                                  first
                                                                                  | omega
                                                                                  | (ring_nf; omega))))) ?finish
  case start =>
    refine ⟨0,μ,?_,fun _ _ => rfl⟩
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_zero]
    exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
      ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm)
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,kept⟩
    have hs := hsel j hj
    have hk := hcandidate (sel j) hs
    have hocc' : ν (occ+j) = (sel j : ℤ) :=
      (kept _ (by omega)).trans (hoccRead j hj)
    have hcan' : ν (candidates+sel j) = (candidate (sel j) : ℤ) :=
      (kept _ (by omega)).trans (hcandidateRead (sel j) hs)
    have hbEnd : j*L+L ≤ J*L := by
      have hh := Nat.mul_le_mul_right L (show j+1 ≤ J by omega)
      simpa only [Nat.succ_mul] using hh
    have hmEnd : 2*L*sel j+L+L ≤ 2*L*M := by
      have hh := Nat.mul_le_mul_left (2*L) (show sel j+1 ≤ M by omega)
      nlinarith
    have htEnd : candidate (sel j)*p+p ≤ K*p := by
      have hh := Nat.mul_le_mul_right p (show candidate (sel j)+1 ≤ K by omega)
      simpa only [Nat.succ_mul] using hh
    have hdoubleNonneg : (0 : ℤ) ≤ 2*(L : ℤ) := by positivity
    have hdoubleWord : 2*(L : ℤ) ≤ lim.word := by
      have hm : 2*L ≤ 2*L*M := Nat.le_mul_of_pos_right _ (by omega)
      exact (by exact_mod_cast (show 2*L ≤ lim.space by omega) :
        2*(L : ℤ) ≤ lim.space).trans hw
    have hmapNonneg : (0 : ℤ) ≤ 2*(L : ℤ)*(sel j : ℤ) := by positivity
    have hmapWord : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast (show 2*L*sel j ≤ lim.space by omega) :
        2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have hmapEndZ : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ rowOut := by
      exact_mod_cast (show maps+2*L*sel j+L+L ≤ rowOut by omega)
    have hbRead : ∀ a < L, ν (bitBase+j*L+a) = (bits (j*L+a) : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (by simpa only [Nat.add_assoc] using hbitsRead (j*L+a) (by omega))
    have hw0 : ∀ a < L, ν (maps+2*L*sel j+a) = (w0 (sel j) a : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (hread0 (sel j) hs a ha)
    have hw1 : ∀ a < L, ν (maps+2*L*sel j+L+a) = (w1 (sel j) a : ℤ) := by
      intro a ha
      exact (kept _ (by omega)).trans (hread1 (sel j) hs a ha)
    have hcL : ∀ r < p, ν (histL+candidate (sel j)*p+r) =
        (leftCount (candidate (sel j)) r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hcountL _ hk r hr)
    have hcR : ∀ r < p, ν (histR+candidate (sel j)*p+r) =
        (rightCount (candidate (sel j)) r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hcountR _ hk r hr)
    have hrow := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets (d := d+1) (μ := ν)
      (src := bitBase+j*L) (src0 := maps+2*L*sel j) (src1 := maps+2*L*sel j+L)
      (L := L) (h := h) (histL := histL+candidate (sel j)*p)
      (histR := histR+candidate (sel j)*p) (p := p) (cap := cap)
      (dst := rowOut) (work := work) (U := U) (V := V)
      S.rowFlagDef S.row S.emod S.flag (fun a => bits (j*L+a))
      (w0 (sel j)) (w1 (sel j)) (leftCount (candidate (sel j))) (rightCount (candidate (sel j)))
      hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega) hrowOut
      hspace hword hbRead hw0 hw1 (fun a ha => hbitBound (j*L+a) (by omega))
      (hbound0 (sel j) hs) (hbound1 (sel j) hs)
      hcL hcR (hcountBoundL _ hk) (hcountBoundR _ hk)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.roundBody
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrow _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrow ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hocc', hcan', _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hocc', hcan', _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hocc', hcan', _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
       on_goal -1 => (rintro q ν₁ ⟨leftRead, rightRead, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hlRead : ν₁ rowOut = (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) := leftRead
    have hrRead : ν₁ (rowOut+1) = (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) := rightRead
    have hlB := hleftPrefix (j+1)
    have hrB := hrightPrefix (j+1)
    have hlCast : (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) j : ℤ)*
        (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount j : ℤ) =
        (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j+1) : ℤ) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_succ,Nat.cast_mul]
    have hrCast : (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) j : ℤ)*
        (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount j : ℤ) =
        (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j+1) : ℤ) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_succ,Nat.cast_mul]
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) (j + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlRead, hlCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hlRead, hlCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlRead, hlCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) (j + 1) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrRead, hrCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hrRead, hrCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrRead, hrCast, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,q,ν₁,by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_⟩
    intro a ha
    exact (hkeep a ⟨by omega,Or.inl ha⟩).trans (kept a ha)
  case done =>
    intro σ hj hshape
    exact hshape
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,_⟩
    simp
  case finish =>
    rintro _ ⟨r,ν,rfl,kept⟩
    have hl := hleftPrefix J
    have hr := hrightPrefix J
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℕ) ?_ ?_ ?_
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (_root_.ThreeSum.SourceFlagProduct.product (_root_.ThreeSum.LightSourceTrim.rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℕ) ?_ ?_ ?_
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
    refine ⟨by simp,by simp,?_⟩
    intro a ⟨ha,hout⟩
    simp only [Function.update_of_ne (show a ≠ dst+1 by omega),
      Function.update_of_ne (show a ≠ dst by omega)]
    exact kept a ha
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs.meets__implementation_932c38d4aa) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.Procs.meets__implementation_932c38d4aa)

#print axioms solution
