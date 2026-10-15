-- Prove2me | solution 1 for ThreeSum.LightZetaCell.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:31:33.916995+00:00
-- url     : https://prove2.me/submissions/8b86c05a-81f2-4d20-83aa-f8da5b458476

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightMaskErase_meets
import Theorems.Thm_ThreeSum_LightSubsetAddress_rank_meets
import Theorems.Thm_ThreeSum_LightSubsetOffset_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_meets
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_le
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators









































































































































































































































theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [layerOffset_succ]
  omega






theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))

























































































































































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)







































end ThreeSum.SubsetAddress

end

section


/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress





























































theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    natPositions (s.erase a) = (natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) = subsetMask (s.erase a) := by
  rw [subsetMask, eraseMask_maskOf _ (natPositions_subset s),
    ← natPositions_erase, ← subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) ≠ subsetMask s ↔ a ∈ s := by
  rw [eraseMask_subsetMask, (subsetMask_injective L).ne_iff, Finset.erase_ne_self]

theorem eraseMask_lt_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) < subsetMask s ↔ a ∈ s := by
  have hb := eraseMask_le (a := a.val) (subsetMask_isMask s).1
  rw [lt_iff_le_and_ne]
  simpa only [hb, true_and] using eraseMask_ne_iff s a

theorem eraseMask_isMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) (ha : a ∈ s) :
    IsMask L (s.card-1) (eraseMask L a.val (subsetMask s)) := by
  rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
  exact subsetMask_isMask (s.erase a)

end ThreeSum.MaskErase

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

























































































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

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

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
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
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
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
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
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
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}


























private theorem rank_offset {L : ℕ} (S : Finset (Fin L)) :
    layerRank L S.card (subsetMask S) + layerOffset L S.card = subsetRank S := by
  simp only [subsetRank, downsetRank, (subsetMask_isMask S).2, Nat.add_comm]

theorem meets_sourceProof {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hThis : P[pThis]? = some (body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pThis d [L,S.card,subsetMask S,a.val,src,dst,work] μ (time L)
      (fun _ μ' => μ' (dst+subsetRank S) = Subset.zetaStep a f S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by
  have hm := subsetMask_isMask S
  have hk := hm.le_width
  have hrS := subsetRank_lt hS
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hfS := abs_le.mp (hvalues S hS)
  have hRankSum : (layerRank L S.card (subsetMask S) : ℤ) +
      (layerOffset L S.card : ℤ) = (subsetRank S : ℤ) := by
    exact_mod_cast rank_offset S
  have hRankNonneg : (0 : ℤ) ≤ layerRank L S.card (subsetMask S) := Int.natCast_nonneg _
  have hOffsetNonneg : (0 : ℤ) ≤ layerOffset L S.card := Int.natCast_nonneg _
  have hcastSize : ((L : ℤ)+1)*((L : ℤ)+1) = (tableSize L : ℤ) := by
    simp [tableSize,pow_two]
  apply Meets.of_body hThis
  unfold body time
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (work + tableSize L : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hcastSize]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcastSize] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcastSize] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hSetup := LightSubsetSetup.meets (d := d+1) (μ := μ) C hw hspace hword₀ hm (by omega)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hSetup _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hSetup ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSubsetSetup.time,
                LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro fullRank μ₁ ⟨hFullRank, hTable, hPowers, hKept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hSread : μ₁ (src+subsetRank S) = f S :=
    (hKept _ (by omega)).trans (hread S hS)
  have hOff := LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega) hword hTable le_rfl hk
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hOff _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hOff ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSubsetSetup.time,
                LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro fullOffset μ₂ ⟨hFullOffset, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₂
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (subsetRank S : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hFullRank, hFullOffset, hRankSum, LightSubsetSetup.time,
                LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hFullRank, hFullOffset, hRankSum, LightSubsetSetup.time,
                LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hFullRank, hFullOffset,
                hRankSum, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hDel := LightMaskErase.meets hErase μ₁ hw hspace hword₀ hPowers
    L a.val (subsetMask S) le_rfl (Nat.le_of_lt a.isLt) hm.1 (d+1) (by omega)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      | refine Light.Ends.callToThen (hDel _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hDel ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightSubsetSetup.time,
                LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              omega)));
    (on_goal -1 =>
        ((rintro erased μ₂ ⟨hErased, hmem⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  subst μ₂
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
        Light.Ends.iteIffThen
          ((eraseMask L a.val (subsetMask S) : ℤ) < (subsetMask S : ℤ))
          (fun hbitZ => ?_) (fun hnotZ => ?_) ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hErased,
                LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hErased, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hErased,
                LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                powTableTime] <;>
              omega)));
    (all_goals
        repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_)
  · have ha : a ∈ S := (eraseMask_lt_iff S a).mp (by exact_mod_cast hbitZ)
    have hkpos : 0 < S.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hsubCard : (S.card : ℤ)-1 = ((S.card-1 : ℕ) : ℤ) := by omega
    have hE : (S.erase a).card ≤ cut := (Finset.card_le_card (Finset.erase_subset _ _)).trans hS
    have hrE := subsetRank_lt hE
    have hfE := abs_le.mp (hvalues (S.erase a) hE)
    have hEread : μ₁ (src+subsetRank (S.erase a)) = f (S.erase a) :=
      (hKept _ (by omega)).trans (hread _ hE)
    have hMask := eraseMask_isMask S a ha
    have hkE : S.card-1 ≤ L := by omega
    have hRankE : (layerRank L (S.card-1) (eraseMask L a.val (subsetMask S)) : ℤ) +
        (layerOffset L (S.card-1) : ℤ) = (subsetRank (S.erase a) : ℤ) := by
      rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
      exact_mod_cast rank_offset (S.erase a)
    have hRankENonneg : (0 : ℤ) ≤ layerRank L (S.card-1) (eraseMask L a.val (subsetMask S)) :=
      Int.natCast_nonneg _
    have hOffsetENonneg : (0 : ℤ) ≤ layerOffset L (S.card-1) := Int.natCast_nonneg _
    have hRankCall := rank_meets C.rank μ₁ hw (by omega) hspace hword₀ hTable hPowers
      L (S.card-1) (eraseMask L a.val (subsetMask S)) le_rfl hMask (d+1) (by omega)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (first
        | refine Light.Ends.callToThen (hRankCall _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hRankCall ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hErased,
                  hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hErased, hsubCard, LightSubsetSetup.time, LightMaskErase.time,
                  rankTime, LightSubsetOffset.time, buildTime, rowTime,
                  LightArray.linearTime, powTableTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hErased, hsubCard,
                  LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                omega)));
      (on_goal -1 =>
          ((rintro erasedRank μ₂ ⟨hErasedRank, hmem⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst μ₂
    have hOffCall := LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega)
      hword hTable le_rfl hkE
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (first
        | refine Light.Ends.callToThen (hOffCall _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hOffCall ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hsubCard,
                  LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                omega)));
      (on_goal -1 =>
          ((rintro erasedOffset μ₂ ⟨hErasedOffset, hmem⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst μ₂
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (subsetRank (S.erase a) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  hErasedRank, hErasedOffset, hRankE, LightSubsetSetup.time,
                  LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                  rowTime, LightArray.linearTime, powTableTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hErasedRank, hErasedOffset, hRankE, LightSubsetSetup.time,
                  LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                  rowTime, LightArray.linearTime, powTableTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hErasedRank, hErasedOffset,
                  hRankE, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                omega)));
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
          Light.Ends.storeToThen (dst + subsetRank S) (f S + f (S.erase a)) ?_ ?_
            ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hSread,
                  hEread, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hSread, hEread, LightSubsetSetup.time, LightMaskErase.time,
                  rankTime, LightSubsetOffset.time, buildTime, rowTime,
                  LightArray.linearTime, powTableTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hSread, hEread,
                  LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_true]
    · intro i hi hne
      change Function.update μ₁ (dst+subsetRank S) (f S + f (S.erase a)) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
  · have ha : a ∉ S := by
      intro ha
      exact hnotZ (by exact_mod_cast (eraseMask_lt_iff S a).mpr ha)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (dst + subsetRank S) (f S) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hSread,
                  LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hSread, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hSread,
                  LightSubsetSetup.time, LightMaskErase.time, rankTime,
                  LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
                  powTableTime] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_false]
    · intro i hi hne
      change Function.update μ₁ (dst+subsetRank S) (f S) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi



























end ThreeSum.LightZetaCell

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pThis)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank)) →
    ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pOffset)
          (@Option.some.{0} Light.Stmt ThreeSum.LightSubsetOffset.body) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
            (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)) →
          ∀ {μ : Nat → Int} {L cut src dst work U d : Nat} (S : Finset.{0} (Fin L)) (a : Fin L)
            (f : Finset.{0} (Fin L) → Int),
            @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
                    (ThreeSum.SubsetAddress.downsetCap L cut))
                  work →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                      (ThreeSum.SubsetAddress.downsetCap L cut))
                    work →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                          (ThreeSum.LightPascal.tableSize L))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      lim.space →
                    @LE.le.{0} Int Int.instLEInt
                        (@Nat.cast.{0} Int instNatCastInt
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        lim.word →
                      @LE.le.{0} Int Int.instLEInt
                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                            (@Nat.cast.{0} Int instNatCastInt U))
                          lim.word →
                        @ThreeSum.LightZetaCell.TableAt L μ src cut f →
                          (∀ (T : Finset.{0} (Fin L)),
                              @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) T) cut →
                                @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f T))
                                  (@Nat.cast.{0} Int instNatCastInt U)) →
                            @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  lim.depth →
                                Light.Meets lim P pThis d
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin L) S))
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.SubsetAddress.subsetMask L S))
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@Fin.val L a))
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                (@List.nil.{0} Int))))))))
                                  μ (ThreeSum.LightZetaCell.time L) fun (x : Int) (μ' : Nat → Int) =>
                                  And
                                    (@Eq.{1} Int
                                      (μ'
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                          (@ThreeSum.SubsetAddress.subsetRank L S)))
                                      (@ThreeSum.Subset.zetaStep.{0} (Fin L) (instDecidableEqFin L) a f S))
                                    (ThreeSum.LightZetaCell.KeptExcept μ μ' work
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                                        (@ThreeSum.SubsetAddress.subsetRank L S))) := by
  exact @ThreeSum.LightZetaCell.meets_sourceProof

#print axioms solution
