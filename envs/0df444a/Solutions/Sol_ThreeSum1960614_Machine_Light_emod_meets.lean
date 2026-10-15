-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.emod_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:18.76076+00:00
-- url     : https://prove2.me/submissions/04df7d0e-42a6-4c33-ad59-754747e787e9

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
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_reduce_ends
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_sign_ends
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_table_ends

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod

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
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
section


/-- **emod(x, M, fr)** returns the remainder of x modulo M and changes no cell below the free
pointer. -/
theorem ThreeSum1960614.Machine.Light.emod_meets__implementation_69a14252b0 {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.emodBody) (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [x, Mo, fr] μ (_root_.Light.emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr := by
  have hword := F.word
  have hax : ((x.natAbs : ℕ) : ℤ) = |x| := Int.natCast_natAbs x
  have haV : x.natAbs ≤ V := by omega
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp ?_
  unfold _root_.Light.emodTime
  generalize x.natAbs = a at hax haV ⊢
  -- count := 0; mult := M; the table; the subtractions; the sign
  have tail : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Count (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Mult (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Modulus)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq _root_.ThreeSum1960614.Machine.Light.emodTable (_root_.ThreeSum1960614.Machine.Light.Stmt.seq _root_.ThreeSum1960614.Machine.Light.emodReduce _root_.ThreeSum1960614.Machine.Light.emodSign))))) ⟨_root_.Light.frame [x, Mo, fr, a], μ⟩ (43 * _root_.Light.emodRounds a Mo + 26) fun σ' =>
      σ'.loc 0 = x % (Mo : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ σ'.mem fr := by
    refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) (_root_.ThreeSum1960614.Machine.Light.Ends.setToThen (Mo : ℕ) ?_)
    refine _root_.ThreeSum1960614.Machine.Light.Ends.next _ ((_root_.ThreeSum1960614.Machine.Light.Emod.table_ends F haV).mono le_rfl ?_)
    rintro _ ⟨μ', rfl, tab⟩
    refine _root_.ThreeSum1960614.Machine.Light.Ends.next _ ((_root_.ThreeSum1960614.Machine.Light.Emod.reduce_ends F haV tab).mono le_rfl ?_)
    rintro _ rfl
    exact (_root_.ThreeSum1960614.Machine.Light.Emod.sign_ends F hax).mono (by (first
                                                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                    first
                                                                                    | omega
                                                                                    | (ring_nf; omega))
                                                                                | omega
                                                                                |
                                                                                  (simp [] <;>
                                                                                      first
                                                                                      | omega
                                                                                      | (ring_nf; omega)))) fun σ' h =>
      ⟨h.1, fun b hb => by rw [h.2]; exact tab.2 b hb⟩
  -- rest := |x|
  refine _root_.ThreeSum1960614.Machine.Light.Ends.iteThen (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    rw [abs_of_neg hneg] at hax
    exact _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (a : ℕ) (tail.mono (by (first
                                                                                      | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                          first
                                                                                          | omega
                                                                                          | (ring_nf; omega))
                                                                                      | omega
                                                                                      |
                                                                                        (simp [] <;>
                                                                                            first
                                                                                            | omega
                                                                                            | (ring_nf; omega)))) fun _ h => h)
  · have hpos : 0 ≤ x := by simpa using hpos
    rw [abs_of_nonneg hpos] at hax
    exact _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (a : ℕ) (tail.mono (by (first
                                                                                      | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                          first
                                                                                          | omega
                                                                                          | (ring_nf; omega))
                                                                                      | omega
                                                                                      |
                                                                                        (simp [] <;>
                                                                                            first
                                                                                            | omega
                                                                                            | (ring_nf; omega)))) fun _ h => h)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.emod_meets__implementation_69a14252b0) := (@ThreeSum1960614.Machine.Light.emod_meets__implementation_69a14252b0)

#print axioms solution
