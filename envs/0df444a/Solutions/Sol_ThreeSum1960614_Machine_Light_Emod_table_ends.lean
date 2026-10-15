-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Emod.table_ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:41.112204+00:00
-- url     : https://prove2.me/submissions/5d185e20-b5e5-4203-9a5c-77bdc9df76f5

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

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























/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ T Q :=
  (_root_.ThreeSum1960614.Machine.Light.Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h





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
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
namespace Emod
open _root_.Light.Emod









end Emod

















/-- The multiple M 2^i is at most a exactly for i below the number of doublings. -/
theorem mul_two_pow_le_iff {a M i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < _root_.Light.emodRounds a M := by
  rw [_root_.Light.emodRounds, Nat.lt_size, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]

/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : _root_.Light.emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [_root_.Light.emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _


namespace Emod
open _root_.Light.Emod






variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

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

/-- **The table.**  With K doublings, the K multiples M 2^j ≤ a are written. -/
theorem ThreeSum1960614.Machine.Light.Emod.table_ends__implementation_04c3e19566 (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr) (haV : a ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.Light.emodTable ⟨_root_.Light.frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * _root_.Light.emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨_root_.Light.frame [x, Mo, fr, a, _root_.Light.emodRounds a Mo, ((Mo * 2 ^ _root_.Light.emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        _root_.ThreeSum1960614.Machine.Light.Emod.Table μ μ' Mo fr (_root_.Light.emodRounds a Mo) := by
  ((obtain ⟨⟩ := _root_.id F))
  have hK : _root_.Light.emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := _root_.ThreeSum1960614.Machine.Light.emodRounds_le haV
  refine _root_.ThreeSum1960614.Machine.Light.Ends.whileConst (fun i σ => ∃ μ',
    σ = ⟨_root_.Light.frame [x, Mo, fr, a, i, ((Mo * 2 ^ i : ℕ) : ℤ)], μ'⟩ ∧ _root_.ThreeSum1960614.Machine.Light.Emod.Table μ μ' Mo fr i)
    (_root_.Light.emodRounds a Mo) _root_.ThreeSum1960614.Machine.Light.emodTableRound.blockCost ?start ?round ?done
    (by simp [_root_.ThreeSum1960614.Machine.Light.emodTableRound]; omega)
  case start => exact ⟨μ, by simp, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
  case done =>
    rintro _ ⟨μ', rfl, tab⟩
    have hgt : ¬ Mo * 2 ^ _root_.Light.emodRounds a Mo ≤ a := fun h =>
      absurd ((_root_.ThreeSum1960614.Machine.Light.mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
    generalize Mo * 2 ^ _root_.Light.emodRounds a Mo = t at hgt
    exact ⟨by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)), by simp; omega, μ', rfl, tab⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, tab, below⟩
    have hle : Mo * 2 ^ i ≤ a := (_root_.ThreeSum1960614.Machine.Light.mul_two_pow_le_iff F.mod_pos).2 hi
    have hnext : Mo * 2 ^ (i + 1) = Mo * 2 ^ i + Mo * 2 ^ i := by ring
    rw [hnext]
    generalize ht : Mo * 2 ^ i = t at hle
    refine ⟨by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                  (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                  simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)), by simp; omega, ?_⟩
    unfold _root_.ThreeSum1960614.Machine.Light.emodTableRound
    -- table[count] := mult; count := count + 1; mult := mult + mult
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (fr + i) t ?_ ?_ ?_
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (t + t : ℕ) ?_ ?_ ?_
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
    refine ⟨_, rfl, fun j hj => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · rw [Function.update_of_ne (by omega)]
        exact tab j h
      · rw [Function.update_self, ht]
    · rw [Function.update_of_ne (by omega)]
      exact below b hb
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Emod.table_ends__implementation_04c3e19566) := (@ThreeSum1960614.Machine.Light.Emod.table_ends__implementation_04c3e19566)

#print axioms solution
