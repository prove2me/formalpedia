-- Prove2me | solution 1 for ThreeSum.LightBandPartition.upper_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:56.542249+00:00
-- url     : https://prove2.me/submissions/14071f49-1f5a-45e4-bc04-326f8c5d707b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩







theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩


































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h








/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by first
                                                                                            |
                                                                                              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                (first
                                                                                                  | omega
                                                                                                  | ((ring_nf); (omega))))
                                                                                            | omega
                                                                                            |
                                                                                              (simp [] <;>
                                                                                                  first
                                                                                                  | omega
                                                                                                  | ((ring_nf); (omega)))) :
    Ends lim P d s σ T Q :=
  h.mono hT rest







































/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

/-! ## Loops whose body is a block -/














/-! ## Counting loops -/











































































end Light

end
end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT





























































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


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

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}











































end

end Light

end
end

section


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

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl




















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]














/-! ## The tactics -/









































end Light

end
end

section


/-!
# Constructing consecutive band endpoints in actual memory

The program computes the number of bands itself. Its quotient loop is charged
linearly in that number, and both endpoint passes issue bounded-address
loads from the sorted source. Output arrays reserve `n` cells each; only the
computed band count is populated.
-/

namespace ThreeSum.LightBandPartition

open Light ThreeSum.BandPartition

variable {lim : Limits} {P : Program}





































theorem upper_meets_sourceProof {p src dst n g d : ℕ} (hp : P[p]? = some upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+size n g ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src,n,g,dst,size n g] μ (upperTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (size n g)) := by
  let F := fun i => f (stop n g i-1)
  apply Meets.of_body hp
  unfold upperBody upperTime
  refine Ends.for
    (fun i σ => ∃ q : ℕ,
      σ = ⟨frame [src,n,g,dst,size n g,i,q],wrote μ dst F i⟩)
    (size n g) 92 ?start ?round ?done ?bound
  case start =>
    refine ⟨0,?_⟩
    simp [update_frame_setLocal,wrote_zero]
    simpa using (frame_append_zeros [src,n,g,dst,size n g,0] 1).symm
  case round =>
    rintro i _ hi _ ⟨q,rfl⟩
    have hidx : i*g < n := start_lt hg hi
    have hsmall : size n g ≤ n := size_le _ _
    have hnextBound : (i+1)*g ≤ n+g := by nlinarith
    have hnextNonneg : (0 : ℤ) ≤ ((i : ℤ)+1)*(g : ℤ) := by positivity
    have hnextWord : ((i : ℤ)+1)*(g : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast (show (i+1)*g ≤ n+g+2 by omega) :
        ((i : ℤ)+1)*(g : ℤ) ≤ ((n+g+2 : ℕ) : ℤ)).trans hword
    have hstopN := stop_le n g i
    have hstopPos : 0 < stop n g i := by have := start_lt_stop hg hi; omega
    have hstopI := stop_sub_one_lt hg hi
    have hstore (q : ℕ) (hq : q = stop n g i) :
        Ends lim P d (.store (((Light.Expr.op Light.Op.add) (v 3) (v 5))) (M (((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v 0) (v 6)) (k 1)))))
          ⟨frame [src,n,g,dst,size n g,i,q],wrote μ dst F i⟩ 40
          (fun σ => σ.loc 5 = (i : ℤ) ∧ ∃ r : ℕ,
            {σ with loc := Function.update σ.loc 5 ((i : ℤ)+1)} =
              ⟨frame [src,n,g,dst,size n g,i+1,r],wrote μ dst F (i+1)⟩) := by
      subst q
      have haddr : ((src : ℤ)+(stop n g i : ℤ)-1).toNat = src+(stop n g i-1) := by
        rw [show (src : ℤ)+(stop n g i : ℤ)-1 = ((src+(stop n g i-1) : ℕ) : ℤ) by omega,
          Int.toNat_natCast]
      have hr : wrote μ dst F i (src+(stop n g i-1)) = F i := by
        rw [wrote_rest (by omega)]
        exact hread _ hstopI
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.storeToThen (dst + i) (F i) ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                    hr]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [haddr, hr] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hr] <;> omega)));
        (try with_unfolding_none refine Light.Ends.skip ?_)
      exact ⟨by simp,stop n g i,by simp [update_frame_setLocal,wrote_succ]⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen ((i + 1) * g : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine
          Light.Ends.iteIffThen ((n : ℤ) < (((i + 1) * g : ℕ) : ℤ)) (fun hn => ?_)
            (fun hn => ?_) ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (all_goals
          repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)
    · have hmin : stop n g i = n := by unfold stop; omega
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
        (try with_unfolding_none refine Light.Ends.skip ?_)
      focus
        ((refine
              Light.Ends.pieceLast (hstore n hmin.symm)
                (fun _ apspMacro_26356_0 => apspMacro_26356_0) ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [] <;>
                    first
                    | omega
                    | ((ring_nf); (omega)))))
    · have hmin : stop n g i = (i+1)*g := by unfold stop; omega
      focus
        ((refine
              Light.Ends.pieceLast (hstore ((i + 1) * g) hmin.symm)
                (fun _ apspMacro_26460_0 => apspMacro_26460_0) ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [] <;>
                    first
                    | omega
                    | ((ring_nf); (omega)))))
  case done =>
    rintro _ _ ⟨q,rfl⟩
    exact ⟨fun i hi => wrote_done (μ := μ) (dst := dst) (f := F) hi,by ((try refine Light.SameOn.cell ?_); (intro apspMacro_26618_0 apspMacro_26618_1);
                                                                             (first
                                                                               |
                                                                                 ((((repeat
                                                                                           (((with_reducible
                                                                                                   rename Light.SameOn _ _ _ => apspMacro_26618_2));
                                                                                             ((try
                                                                                                   have :=
                                                                                                     apspMacro_26618_2 apspMacro_26618_0 (by omega)));
                                                                                             (revert apspMacro_26618_2)));
                                                                                       (intros);
                                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                   (omega))
                                                                               |
                                                                                 ((simp [] at apspMacro_26618_1);
                                                                                   (((repeat
                                                                                           (((with_reducible
                                                                                                   rename Light.SameOn _ _ _ => apspMacro_26618_3));
                                                                                             ((try
                                                                                                   have :=
                                                                                                     apspMacro_26618_3 apspMacro_26618_0 (by omega)));
                                                                                             (revert apspMacro_26618_3)));
                                                                                       (intros);
                                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                   (omega))
                                                                               |
                                                                                 ((((repeat
                                                                                           (((with_reducible
                                                                                                   rename Light.SameOn _ _ _ => apspMacro_26618_4));
                                                                                             ((try
                                                                                                   have :=
                                                                                                     apspMacro_26618_4 apspMacro_26618_0 (by omega)));
                                                                                             (revert apspMacro_26618_4)));
                                                                                       (intros);
                                                                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                   (fail
                                                                                       "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                 SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                 its condition K x does not follow from the hypotheses."))))⟩
  case bound =>
    rintro i _ _ _ ⟨q,rfl⟩
    simp




















































































end ThreeSum.LightBandPartition

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {p src dst n g d : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightBandPartition.upperBody) →
    ∀ (μ f : Nat → Int),
      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) dst →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst (ThreeSum.BandPartition.size n g))
                lim.space →
              @LE.le.{0} Int Int.instLEInt
                  (@Nat.cast.{0} Int instNatCastInt
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n g)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  lim.word →
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i n →
                      @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)) (f i)) →
                  Light.Meets lim P p d
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size n g))
                              (@List.nil.{0} Int))))))
                    μ (ThreeSum.LightBandPartition.upperTime (ThreeSum.BandPartition.size n g))
                    fun (x : Int) (μ' : Nat → Int) =>
                    And
                      (∀ (i : Nat),
                        @LT.lt.{0} Nat instLTNat i (ThreeSum.BandPartition.size n g) →
                          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
                            (f
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (ThreeSum.BandPartition.stop n g i)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Light.SameOutside μ μ' dst (ThreeSum.BandPartition.size n g)) := by
  exact @ThreeSum.LightBandPartition.upper_meets_sourceProof

#print axioms solution
