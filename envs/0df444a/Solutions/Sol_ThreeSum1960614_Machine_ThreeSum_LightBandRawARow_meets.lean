-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:48:31.476394+00:00
-- url     : https://prove2.me/submissions/68dc6ffc-e2d4-43bc-b798-45a8a9944d8a

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace Light.Copy
end Light.Copy
namespace Light.Fill
end Light.Fill
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBandRawARow
end ThreeSum.LightBandRawARow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawARow
end ThreeSum1960614.Machine.ThreeSum.LightBandRawARow

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
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : _root_.ThreeSum1960614.Machine.Light.Seg (_root_.Light.wrote μ dst f n) dst l := fun i hi => by
  rw [_root_.ThreeSum1960614.Machine.Light.wrote_done (hl ▸ hi), h i hi]





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## copy -/

namespace Copy
open _root_.Light.Copy







end Copy





/-- **copy(src, dst, n)** copies the n cells from src to dst and changes nothing else. -/
theorem copy_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst n) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(src : ℤ), dst, n] μ (_root_.Light.copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n := by
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => _root_.ThreeSum1960614.Machine.Light.wrote_done (f := fun i => μ (src + i)) hi, by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
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
                                                                                                                       its condition K x does not follow from the hypotheses.")))⟩ hw hdst rfl rfl
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.copyTime]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.Light.copyTime] <;>
                     first
                     | omega
                     | (ring_nf; omega)))))
  -- Round i reads src[i], which no earlier round has written.
  have hread : _root_.Light.wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))

/-! ## fill -/

namespace Fill
open _root_.Light.Fill







end Fill





/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), n, x] μ (_root_.Light.fillTime n) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (List.replicate n x) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n :=
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun _ => x) (fun i hi => by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    ⟨_root_.ThreeSum1960614.Machine.Light.seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
                                                                                                                       intro p2m_macro_16777210159978675910 p2m_macro_2988969938304694299
                                                                                                                       first
                                                                                                                       | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_5136075375632954890); (try have := p2m_macro_5136075375632954890 p2m_macro_16777210159978675910 (by omega)); revert p2m_macro_5136075375632954890)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       |
                                                                                                                         (simp [] at p2m_macro_2988969938304694299;
                                                                                                                           ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_15352015378803141894); (try have := p2m_macro_15352015378803141894 p2m_macro_16777210159978675910 (by omega)); revert p2m_macro_15352015378803141894)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_6492236951704766786); (try have := p2m_macro_6492236951704766786 p2m_macro_16777210159978675910 (by omega)); revert p2m_macro_6492236951704766786)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                                                                                                                           fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                                                       its condition K x does not follow from the hypotheses.")))⟩
    hw hdst rfl rfl (hT := by (first
                               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.fillTime]
                                   first
                                   | omega
                                   | (ring_nf; omega))
                               | omega
                               |
                                 (simp [_root_.Light.fillTime] <;>
                                     first
                                     | omega
                                     | (ring_nf; omega)))))

end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandRawARow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawARow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.meets__implementation_af6d4a7fea {pMain pCopy pFill : ℕ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.body pCopy pFill))
    (hcopy : P[pCopy]?=some _root_.ThreeSum1960614.Machine.Light.copyBody) (hfill : P[pFill]?=some _root_.ThreeSum1960614.Machine.Light.fillBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ values) (hvalues : values+n ≤ owners)
    (howners : owners+n ≤ positions) (hspace : positions+n ≤ lim.space)
    (hstart : start+n ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,values,owners,positions,n,owner,start] μ (_root_.ThreeSum.LightBandRawARow.time n)
      (fun _ ν =>
        (∀ j < n, ν (values+j)=μ (src+j) ∧
          ν (owners+j)=(owner : ℤ) ∧ ν (positions+j)=((start+j : ℕ) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.KeptOthers μ ν values owners positions n) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.body _root_.ThreeSum.LightBandRawARow.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.copy_meets (d := d + 1) (μ := μ) (src := src) (dst := values) (n := n) hcopy hw (by omega) (by omega) (Or.inl hsrc)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.copy_meets (d := d + 1) (μ := μ) (src := src) (dst := values) (n := n) hcopy hw (by omega) (by omega) (Or.inl hsrc)) ?_ ?_ ?_ ?_
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
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro unused ν₁ ⟨hcopied, hkeepCopy⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := ν₁) (dst := owners) (n := n) (x := (owner : ℤ)) hfill hw (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := ν₁) (dst := owners) (n := n) (x := (owner : ℤ)) hfill hw (by omega)) ?_ ?_ ?_ ?_
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
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro unused ν₂ ⟨hfilled, hkeepFill⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pass (fun j => ((start+j : ℕ) : ℤ)) (fun j hj => ?_)
    ?_ hw hspace rfl rfl (hT := by (first
                                    | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.copyTime, _root_.Light.fillTime]
                                        first
                                        | omega
                                        | (ring_nf; omega))
                                    | omega
                                    |
                                      (simp [_root_.Light.copyTime, _root_.Light.fillTime] <;>
                                          first
                                          | omega
                                          | (ring_nf; omega))))
  · (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  · dsimp only
    constructor
    · intro j hj
      constructor
      · rw [_root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega),hkeepFill _ (Or.inl (by omega))]
        exact hcopied j hj
      · constructor
        · rw [_root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)]
          exact (hfilled j (by simpa using hj)).trans (List.getElem_replicate ..)
        · exact _root_.ThreeSum1960614.Machine.Light.wrote_done hj
    · intro a ha
      rw [_root_.ThreeSum1960614.Machine.Light.wrote_rest ha.2.2,hkeepFill a ha.2.1,hkeepCopy a ha.1]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.meets__implementation_af6d4a7fea) := (@ThreeSum1960614.Machine.ThreeSum.LightBandRawARow.meets__implementation_af6d4a7fea)

#print axioms solution
