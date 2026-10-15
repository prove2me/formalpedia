-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Exec.bounded
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:45.512517+00:00
-- url     : https://prove2.me/submissions/ae779c3a-ac96-49bc-8c2a-90c71437a892

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.SplitIfs

namespace Light
end Light
namespace List
end List
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.List
end ThreeSum1960614.Machine.List
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List
open _root_.List


variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]

















/-! ## Blocks one after the other -/

















/-! ## Sums -/













section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]





end









/-! ## A running minimum -/





/-! ## Counting -/

















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp
open _root_.ThreeSumApsp


variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/







/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  _root_.ThreeSum1960614.Machine.List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/





end ThreeSumApsp

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/

public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

section

/-- Writing a bounded number into a bounded function. -/
private theorem private_25b169e592_abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]
end


/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : _root_.ThreeSum1960614.Machine.Light.State} (hσ : σ.Bounded lim) :
    ∀ e : _root_.ThreeSum1960614.Machine.Light.Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n, h => by
    rw [_root_.ThreeSum1960614.Machine.Light.Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | _root_.ThreeSum1960614.Machine.Light.Expr.var x, _ => hσ.1 x
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ _ _, h => h.2.2
  | _root_.ThreeSum1960614.Machine.Light.Expr.load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : _root_.ThreeSum1960614.Machine.Light.State.Bounded lim ⟨_root_.Light.frame args, μ⟩ :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : _root_.ThreeSum1960614.Machine.Light.State} (hσ : σ.Bounded lim) (args : List _root_.ThreeSum1960614.Machine.Light.Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : _root_.ThreeSum1960614.Machine.Light.State.Bounded lim ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ := by
  refine _root_.ThreeSum1960614.Machine.Light.bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact _root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ e (ha e he)





end Light

end

end ThreeSum1960614.Machine

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


/-- A run that starts with words in all variables and cells ends with words in all of them. -/
theorem ThreeSum1960614.Machine.Light.Exec.bounded__implementation_f52c3f5ec2 {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨_root_.ThreeSum1960614.Machine.Light.private_25b169e592_abs_update_le hσ.1 (_root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, _root_.ThreeSum1960614.Machine.Light.private_25b169e592_abs_update_le hσ.2 (_root_.ThreeSum1960614.Machine.Light.Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (_root_.ThreeSum1960614.Machine.Light.bounded_callFrame hσ _ ha)
    exact ⟨_root_.ThreeSum1960614.Machine.Light.private_25b169e592_abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Exec.bounded__implementation_f52c3f5ec2) := (@ThreeSum1960614.Machine.Light.Exec.bounded__implementation_f52c3f5ec2)

#print axioms solution
