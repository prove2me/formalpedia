-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:19.145688+00:00
-- url     : https://prove2.me/submissions/eae39496-b118-4a06-9072-f57521cad3b5

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightRadixDigit
end ThreeSum.LightRadixDigit
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixDigit
end ThreeSum1960614.Machine.ThreeSum.LightRadixDigit

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

open _root_.ThreeSum.LightRadixDigit
open _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets__implementation_f53133f632 {pMain pDivide k b p : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (_root_.ThreeSum.LightRadixDigit.word k b p : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,b,p] μ (_root_.ThreeSum.LightRadixDigit.time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) := by
  have hq : k/b ≤ k := Nat.div_le_self k b
  have hq2 : (k/b)/p ≤ k/b := Nat.div_le_self (k/b) p
  have hprod : ((k/b)/p)*p ≤ k/b := Nat.div_mul_le_self (k/b) p
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum.LightRadixDigit.word k b p) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hw1 := hbudget (k+b+2) (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hw2 := hbudget (k/b+p+2) (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hkWord := hbudget k (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hbWord := hbudget b (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hpWord := hbudget p (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hqWord := hbudget (k/b) (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hq2Word := hbudget ((k/b)/p) (by unfold _root_.ThreeSum.LightRadixDigit.word; omega)
  have hprodWord : (((k/b)/p : ℕ) : ℤ)*(p : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast hprod : (((k/b)/p : ℕ) : ℤ)*(p : ℤ) ≤ (k/b : ℕ)).trans hqWord
  have hprodNonneg : (0 : ℤ) ≤ (((k/b)/p : ℕ) : ℤ)*(p : ℤ) := by positivity
  have hrem : ((k/b : ℕ) : ℤ)-(((k/b)/p : ℕ) : ℤ)*p = (((k/b)%p : ℕ) : ℤ) := by
    have hh := Nat.mod_add_div (k/b) p
    have he : (k/b)%p+((k/b)/p)*p=k/b := by simpa only [Nat.mul_comm] using hh
    exact_mod_cast (by omega : k/b-((k/b)/p)*p=(k/b)%p)
  have hprodIntWord : (k : ℤ)/(b : ℤ)/(p : ℤ)*(p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv] using hprodWord
  have hprodIntNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)/(p : ℤ)*(p : ℤ) := by
    simpa only [Int.natCast_ediv] using hprodNonneg
  have hremInt : (k : ℤ)/(b : ℤ)-(k : ℤ)/(b : ℤ)/(p : ℤ)*p =
      (((k/b)%p : ℕ) : ℤ) := by
    simpa only [Int.natCast_ediv] using hrem
  have hqNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ) := by
    rw [← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hq2Nonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)/(p : ℤ) := by
    rw [← Int.natCast_ediv,← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hmodWord := hbudget ((k/b)%p) (by
    have hm := Nat.mod_le (k/b) p
    unfold _root_.ThreeSum.LightRadixDigit.word
    omega)
  have hmodIntNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)%(p : ℤ) := by
    exact_mod_cast Nat.zero_le ((k/b)%p)
  have hmodIntWord : (k : ℤ)/(b : ℤ)%(p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv,Int.natCast_emod] using hmodWord
  have htime1 : _root_.ThreeSum.LightSmallDivide.time k b ≤ 20*(k+1)+20 := by
    unfold _root_.ThreeSum.LightSmallDivide.time
    omega
  have htime2 : _root_.ThreeSum.LightSmallDivide.time (k/b) p ≤ 20*(k+1)+20 := by
    unfold _root_.ThreeSum.LightSmallDivide.time
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.body _root_.ThreeSum.LightRadixDigit.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := k) (b := b) hdivide μ hw1) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := k) (b := b) hdivide μ hw1) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro q μ₁ ⟨hqval, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  subst q
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := k / b) (b := p) hdivide μ hw2) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := k / b) (b := p) hdivide μ hw2) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro q2 μ₂ ⟨hq2val, hmem₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  subst q2
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((k / b) % p : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrem, hremInt, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrem, hremInt, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrem, hremInt, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨rfl,rfl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets__implementation_f53133f632) := (@ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.meets__implementation_f53133f632)

#print axioms solution
