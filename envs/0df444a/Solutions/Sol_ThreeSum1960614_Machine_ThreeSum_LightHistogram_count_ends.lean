-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:21:59.125982+00:00
-- url     : https://prove2.me/submissions/bba39a99-5e89-4b72-b15a-b52f6ce14672

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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram

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



















/-- A store at the end of the program. -/
theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : _root_.ThreeSum1960614.Machine.Light.Expr} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                                                         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                                                         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by (first
                                         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                             first
                                             | omega
                                             | (ring_nf; omega))
                                         | omega
                                         |
                                           (simp [] <;>
                                               first
                                               | omega
                                               | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) ⟨loc, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.store hs.1 hs.2.1 hs.2.2 hT h









/-! ## Loops whose body is a block -/



/-! ## Counting loops -/





/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : _root_.ThreeSum1960614.Machine.Light.Expr} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {T : ℕ}
    {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem count_zero (key : ℕ → ℕ) (r : ℕ) : _root_.ThreeSum.LightHistogram.count key r 0 = 0 := by
  simp [_root_.ThreeSum.LightHistogram.count]

theorem count_le (key : ℕ → ℕ) (r i : ℕ) : _root_.ThreeSum.LightHistogram.count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    _root_.ThreeSum.LightHistogram.count key r (i + 1) = _root_.ThreeSum.LightHistogram.count key r i + if key i = r then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]













end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends__implementation_9971a41202 {μ : ℕ → ℤ} {loc : ℕ → ℤ} {src dst n p : ℕ}
    (key : ℕ → ℕ) (hsrc : loc 0 = src) (hdst : loc 1 = dst) (hlen : loc 2 = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst + r) = 0) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.countBody ⟨loc, μ⟩ (_root_.ThreeSum.LightHistogram.countTime n) fun σ' =>
      (∀ r < p, σ'.mem (dst + r) = _root_.ThreeSum.LightHistogram.count key r n) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ σ'.mem dst p := by
  let Inv := fun i (μ' : ℕ → ℤ) =>
    (∀ r < p, μ' (dst + r) = _root_.ThreeSum.LightHistogram.count key r i) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.countBody
  apply _root_.ThreeSum1960614.Machine.Light.Ends.forMem Inv n 16 (hn := by omega)
    (hT := by unfold _root_.ThreeSum.LightHistogram.countTime; (first
                                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                    first
                                                                    | omega
                                                                    | (ring_nf; omega))
                                                                | omega
                                                                |
                                                                  (simp [] <;>
                                                                      first
                                                                      | omega
                                                                      | (ring_nf; omega))))
  · exact ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_zero, Nat.cast_zero] using hzero, fun _ _ => rfl⟩
  · intro i μ' hi hI
    obtain ⟨hcnt, hsame⟩ := hI
    have hki := hkeyLt i hi
    have hread : μ' (src + i) = key i :=
      (hsame _ (by omega)).trans (hkeys i hi)
    have hcell := hcnt (key i) hki
    have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le key (key i) i
    have hq0 : (0 : ℤ) ≤ _root_.ThreeSum.LightHistogram.count key (key i) i := Int.natCast_nonneg _
    have hqle : (_root_.ThreeSum.LightHistogram.count key (key i) i : ℤ) < n := by exact_mod_cast hcount.trans_lt hi
    have ha : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4))))).val ⟨Function.update loc 4 (i : ℤ), μ'⟩ =
        ((dst + key i : ℕ) : ℤ) := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread] <;> omega))
    have hv : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4))))) (_root_.ThreeSum1960614.Machine.Light.k 1))).val
        ⟨Function.update loc 4 (i : ℤ), μ'⟩ = ((_root_.ThreeSum.LightHistogram.count key (key i) i + 1 : ℕ) : ℤ) := by
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread, hcell] <;> omega))
    refine _root_.ThreeSum1960614.Machine.Light.Ends.storeLast ?_ (by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                                         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                                         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsrc, hdst, hread, hcell] <;> omega))) (by (first
                                                                                                                  | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                                      first
                                                                                                                      | omega
                                                                                                                      | (ring_nf; omega))
                                                                                                                  | omega
                                                                                                                  |
                                                                                                                    (simp [] <;>
                                                                                                                        first
                                                                                                                        | omega
                                                                                                                        | (ring_nf; omega))))
    change Function.update loc 4 (i : ℤ) = Function.update loc 4 (i : ℤ) ∧
      Inv (i + 1) (Function.update μ' ((((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4))))).val
        ⟨Function.update loc 4 (i : ℤ), μ'⟩).toNat
        ((((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 4))))) (_root_.ThreeSum1960614.Machine.Light.k 1))).val ⟨Function.update loc 4 (i : ℤ), μ'⟩))
    rw [ha, hv, Int.toNat_natCast]
    refine ⟨rfl, ?_, ?_⟩
    · intro r hr
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_succ]
      by_cases heq : key i = r
      · subst r
        simp [Function.update_self]
      · rw [Function.update_of_ne (by omega), hcnt r hr]
        simp [heq]
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact hsame a ha
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends__implementation_9971a41202) := (@ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends__implementation_9971a41202)

#print axioms solution
