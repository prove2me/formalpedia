-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:26.904305+00:00
-- url     : https://prove2.me/submissions/5fd756c8-51ea-4b70-bfea-0a4de6fc2de5

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightCoverUpdate
end ThreeSum.LightCoverUpdate
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate
end ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCoverUpdate
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.meets__implementation_d5080ba204 {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.body)
    {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row+n ≤ lim.space) (hactive : activePtr+n ≤ lim.space)
    (hsep : _root_.Light.Apart row n activePtr n)
    (hread : ∀ j < n, μ (row+j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr+j) = (active j : ℤ))
    (hcover : ∀ j < n, cover j ≤ 1) (hact : ∀ j < n, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [row,activePtr,n] μ (_root_.ThreeSum.LightCoverUpdate.time n)
      (fun _ μ' => (∀ j < n, μ' (activePtr+j) = ((active j*(1-cover j) : ℕ) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' activePtr n) := by
  have he (j : ℕ) (hj : j < n) :
      ((active j*(1-cover j) : ℕ) : ℤ) = (active j : ℤ)*(1-(cover j : ℤ)) := by
    rw [Nat.cast_mul,Nat.cast_sub (hcover j hj)]
    norm_num
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass
    (fun j => (active j : ℤ)*(1-(cover j : ℤ))) (fun j hj => ?_)
    ⟨fun j hj => (_root_.ThreeSum1960614.Machine.Light.wrote_done (μ := μ) (dst := activePtr)
      (f := fun j => (active j : ℤ)*(1-(cover j : ℤ))) hj).trans (he j hj).symm,by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
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
                                                                                                      its condition K x does not follow from the hypotheses.")))⟩ hw hactive rfl rfl
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverUpdate.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightCoverUpdate.time] <;>
                     first
                     | omega
                     | (ring_nf; omega)))))
  have hr : _root_.Light.wrote μ activePtr (fun j => (active j : ℤ)*(1-(cover j : ℤ))) j (row+j) = μ (row+j) :=
    _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  have ha : _root_.Light.wrote μ activePtr (fun j => (active j : ℤ)*(1-(cover j : ℤ))) j (activePtr+j) = μ (activePtr+j) :=
    _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  have hrc := hread j hj
  have hac := hreadActive j hj
  have hc := hcover j hj
  have hav := hact j hj
  have hcZ : (0 : ℤ) ≤ 1-(cover j : ℤ) ∧ 1-(cover j : ℤ) ≤ 1 := by omega
  have hpZ : (0 : ℤ) ≤ (active j : ℤ)*(1-(cover j : ℤ)) ∧
      (active j : ℤ)*(1-(cover j : ℤ)) ≤ 1 := by
    constructor
    · exact mul_nonneg (Int.natCast_nonneg _) hcZ.1
    · exact (mul_le_mul (by exact_mod_cast hav : (active j : ℤ) ≤ 1) hcZ.2 hcZ.1 (by norm_num)).trans (by norm_num)
  (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, ha, hrc, hac] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.meets__implementation_d5080ba204) := (@ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.meets__implementation_d5080ba204)

#print axioms solution
