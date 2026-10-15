-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:42.620458+00:00
-- url     : https://prove2.me/submissions/38a04ee2-61b5-4219-884c-bea54791bd7f

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceMaskFlags_Procs_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceFlagArray
end ThreeSum.LightSourceFlagArray
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
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

namespace ThreeSum1960614.Machine

/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray
open _root_.ThreeSum.LightSourceFlagArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000



theorem flag_le (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) :
    _root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 counts mask ≤ 1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct.product_le _ (fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.rowFlag_le ..) le_rfl









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightSourceFlagArray

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceFlagArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets__implementation_3d18230211 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+4 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ dst) (hmaps : maps+2*L*M ≤ dst)
    (hcandidates : candidates+M ≤ dst)
    (hleft : histL+K*p ≤ dst) (hright : histR+K*p ≤ dst)
    (hmasks : masks+n ≤ dst) (hdst : dst+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskBound : ∀ i < n, mask i < 2^(J*L)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,masks,n,dst,bitBase,rowOut,work]
      μ (_root_.ThreeSum.LightSourceFlagArray.time n J L U) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
        (∀ i < n, ν (dst+n+i) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν bitBase dst (2*n+2)) := by
  have hspace' : work ≤ lim.space := by
    unfold _root_.ThreeSum.LightSourceMaskFlags.space at hspace
    omega
  have hone : (1 : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 1 ≤ lim.space by omega)).trans hw
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.body _root_.ThreeSum.LightSourceFlagArray.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Inv μ J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work
    sel candidate mask w0 w1 leftCount rightCount) n
    (_root_.ThreeSum.LightSourceMaskFlags.time J L U+192) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
        ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm)
    · intro j hj; omega
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,leftWritten,rightWritten,kept⟩
    have hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst := by
      intro a ha
      exact kept a ⟨by omega,Or.inl ha⟩
    have hocc' : ∀ j < J, ν (occ+j) = (sel j : ℤ) := by
      intro j hj
      exact (hkeep _ (by omega)).trans (hoccRead j hj)
    have hcan' : ∀ s < M, ν (candidates+s) = (candidate s : ℤ) := by
      intro s hs
      exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
    have hread0' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+a) = (w0 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
    have hread1' : ∀ s < M, ∀ a < L, ν (maps+2*L*s+L+a) = (w1 s a : ℤ) := by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2*L) (show s+1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
    have hcountL' : ∀ k < K, ∀ r < p, ν (histL+k*p+r) = (leftCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
    have hcountR' : ∀ k < K, ∀ r < p, ν (histR+k*p+r) = (rightCount k r : ℤ) := by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k+1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
    have hmask : ν (masks+i) = (mask i : ℤ) :=
      (hkeep _ (by omega)).trans (hmaskRead i hi)
    have hrun := S.flagProcs.meets (d := d+1) (μ := ν)
      (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (mask := mask i)
      (dst := dst+2*n) (bitBase := bitBase) (rowOut := rowOut) (work := work)
      (U := U) (V := V) (M := M) (K := K)
      sel candidate w0 w1 leftCount rightCount hw (by omega) hp hh
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbits hrowOut hspace hword
      (hmaskBound i hi) hsel hcandidate hocc' hcan' hread0' hread1' hbound0 hbound1
      hcountL' hcountR' hcountBoundL hcountBoundR
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hmask, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
       on_goal -1 => (rintro q ν₁ ⟨left, right, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hl : ν₁ (dst+2*n) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) := left
    have hr : ν₁ (dst+2*n+1) = (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := right
    have hlB := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.flag_le J L h p cap sel candidate w0 w1 leftCount (mask i)
    have hrB := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.flag_le J L h p cap sel candidate w1 w0 rightCount (mask i)
    have haddr : ((dst : ℤ)+2*(n : ℤ)).toNat = dst+2*n := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using Int.toNat_natCast (dst+2*n)
    have haddrR : ((dst : ℤ)+2*(n : ℤ)+1).toNat = dst+2*n+1 := by
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using Int.toNat_natCast (dst+2*n+1)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + i) (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl, haddr, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hl, haddr, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl, haddr, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hr' : Function.update ν₁ (dst+i)
        (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) (dst+2*n+1) =
        (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := by
      rw [Function.update_of_ne (by omega)]
      exact hr
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + n + i) (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr', haddrR, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hr', haddrR, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr', haddrR, _root_.ThreeSum.LightSourceMaskFlags.time, _root_.ThreeSum.LightMaskBits.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSourceTrim.time, _root_.ThreeSum.LightSourceRowFlag.time, _root_.ThreeSum.LightSourceRowScan.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightSourceFlagTest.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,q,Function.update
      (Function.update ν₁ (dst+i) (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ))
      (dst+n+i) (_root_.ThreeSum.LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ),
      by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftWritten j hj)
      · simp
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (rightWritten j hj)
      · simp
    · intro a ⟨ha,hout⟩
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact (kept₁ a ⟨ha,by omega⟩).trans (kept a ⟨ha,hout⟩)
  case done =>
    rintro _ _ ⟨r,ν,rfl,left,right,kept⟩
    exact ⟨left,right,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_,_⟩
    simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets__implementation_3d18230211) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.Procs.meets__implementation_3d18230211)

#print axioms solution
