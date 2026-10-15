-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Ends.of_blockSafe
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:15:33.739762+00:00
-- url     : https://prove2.me/submissions/52ca6813-009e-4a4e-a7e1-b9d4c5d07ecd

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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

namespace Light
end Light
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light

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

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.Light.Ends.of_blockSafe__implementation_89a79a0685 : ∀ {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip, _, _, _, _, _, h => _root_.ThreeSum1960614.Machine.Light.Ends.skip h
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set _ _, _, _, _, hs, hT, h => _root_.ThreeSum1960614.Machine.Light.Ends.set hs hT h
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store _ _, _, _, _, hs, hT, h => _root_.ThreeSum1960614.Machine.Light.Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t, _, _, _, hs, hT, h =>
    _root_.ThreeSum1960614.Machine.Light.Ends.seq s.blockCost t.blockCost
      (of_blockSafe__implementation_89a79a0685 hs.1 le_rfl (of_blockSafe__implementation_89a79a0685 hs.2 le_rfl h)) hT
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t, σ, _, _, hs, hT, h =>
    _root_.ThreeSum1960614.Machine.Light.Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => of_blockSafe__implementation_89a79a0685 (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [_root_.ThreeSum1960614.Machine.Light.Stmt.after, if_pos hc] using h))
      (fun hc => of_blockSafe__implementation_89a79a0685 (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [_root_.ThreeSum1960614.Machine.Light.Stmt.after, if_neg hc] using h))
      hT
  | _root_.ThreeSum1960614.Machine.Light.Stmt.while _ _, _, _, _, hs, _, _ => hs.elim
  | _root_.ThreeSum1960614.Machine.Light.Stmt.call _ _ _, _, _, _, hs, _, _ => hs.elim
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Ends.of_blockSafe__implementation_89a79a0685) := (@ThreeSum1960614.Machine.Light.Ends.of_blockSafe__implementation_89a79a0685)

#print axioms solution
