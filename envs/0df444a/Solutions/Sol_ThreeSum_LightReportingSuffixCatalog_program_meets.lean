-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixCatalog.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:12:05.413009+00:00
-- url     : https://prove2.me/submissions/1e560db6-53b8-41c3-807b-dbc7742bfd24

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightReportingSuffixSetup_program_meets
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
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h














/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

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

















/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

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




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl


















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

end
end

section


/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode

variable {lim : Limits} {P : Program}

theorem storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightZetaStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*downsetCap W cut+subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)













































































































































end ThreeSum.LightSignedLeafBatch

end

section


/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds

open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators











































theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*downsetCap W cut+subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds

end

section


/-!
# Actual construction of a contiguous suffix-box catalog

Each input record is a physical pair of global prefix masks. The host invokes
complete suffix-local setup for every record, writes the corresponding table
pointer, and retains every previous table. The table stride is the exact
local-width storage size; the following setup host computes it explicitly.
-/

namespace ThreeSum.LightReportingSuffixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds

set_option maxHeartbeats 1800000

variable {lim : Limits}




























theorem program_meets_sourceProof
    {μ : ℕ → ℤ} {W V offset cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ ptrBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ ptrBase)
    (hinL : inL+n ≤ ptrBase) (hinR : inR+n ≤ ptrBase)
    (hptr : ptrBase+n ≤ boxBase) (hbox : boxBase+n*stride V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : ∀ i < n, (preL i).card = cL) (hcardR : ∀ i < n, (preR i).card = cR)
    (hpreL : cL+boxCut ≤ cut) (hpreR : cR+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (preL i) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (subsetMask (preR i) : ℤ))
    (hd : d+W+12 ≤ lim.depth) :
    Meets lim program 30 d
      [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
        ptrBase,boxBase,stride V boxCut,maskBase,work]
      μ (time W V boxCut offset n)
      (fun _ μ' =>
        SegN μ' ptrBase (List.ofFn fun i : Fin n => boxBase+i.val*stride V boxCut) ∧
        (∀ i < n, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
          (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
        LightZetaStages.StoredThrough μ' baseL cut f W ∧
        LightZetaStages.StoredThrough μ' baseR cut g W ∧
        Kept μ μ' ptrBase) := by
  have hmask (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hpow : (2^W : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hs := (Nat.le_of_lt (subsetMask_isMask S).1).trans hpow
    exact (by exact_mod_cast hs : (subsetMask S : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body (p := 30) (by rfl : program[30]? = some (body 29))
  unfold body time
  refine Ends.for (lim := lim) (P := program) (d := d) (i := 18) (hi := v 12) (body := roundBody 29)
    (Inv hfit μ preL preR f g cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work)
    n (LightReportingSuffixSetup.time W V boxCut offset+160) ?start ?round ?done ?bound (hT := by first
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
                                                                                                        | ((ring_nf); (omega))))
  case start =>
    refine ⟨0,0,0,0,μ,?_,by simp,by simp,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
      ptrBase,boxBase,stride V boxCut,maskBase,work,0] =
      frame ([(W : ℤ),cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
        ptrBase,boxBase,stride V boxCut,maskBase,work,0] ++ [0,0,0,0])
    exact (frame_append_zeros _ 4).symm
  case round =>
    rintro j _ hj _ ⟨a,b,addr,r,μ',rfl,hptrs,hboxes,hkeep⟩
    have htable : boxBase+j*stride V boxCut+stride V boxCut ≤ maskBase := by
      have hm := Nat.mul_le_mul_right (stride V boxCut) (show j+1 ≤ n by omega)
      nlinarith
    have hwriteBelow : ptrBase+j < boxBase+j*stride V boxCut := by omega
    have hcl := hcardL j hj
    have hcr := hcardR j hj
    have hlread : μ' (inL+j) = (subsetMask (preL j) : ℤ) :=
      (hkeep _ (by omega)).trans (hreadL j hj)
    have hrread : μ' (inR+j) = (subsetMask (preR j) : ℤ) :=
      (hkeep _ (by omega)).trans (hreadR j hj)
    have hlword := hmask (preL j)
    have hrword := hmask (preR j)
    have hstoredL' := LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro i _ hi; exact hkeep i (by omega))
    have hstoredR' := LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro i _ hi; exact hkeep i (by omega))
    unfold roundBody
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (subsetMask (preL j) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlread,
                  LightReportingSuffixSetup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hlread, LightReportingSuffixSetup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hlread,
                  LightReportingSuffixSetup.time] <;>
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
      (refine Light.Ends.setToThen (subsetMask (preR j) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrread,
                  LightReportingSuffixSetup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hrread, LightReportingSuffixSetup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hrread,
                  LightReportingSuffixSetup.time] <;>
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
      (refine Light.Ends.setToThen (boxBase + j * stride V boxCut : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingSuffixSetup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingSuffixSetup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingSuffixSetup.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hcall := (LightReportingSuffixSetup.program_meets (d := d+1) (μ := μ')
      (boxBase := boxBase+j*stride V boxCut) hfit (preL j) (preR j) f g hw hcut hboxCut hstage
      (by omega) (by omega) htable hmasks hspace hword hvalueWord
      (by simpa only [hcl] using hpreL) (by simpa only [hcr] using hpreR)
      hf hg hstoredL' hstoredR' (by omega)).append [body 29]
    rw [hcl,hcr] at hcall
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
        | refine Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hcall ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingSuffixSetup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingSuffixSetup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingSuffixSetup.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro result ν ⟨hnew, hLs, hRs, hkeepCall⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
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
          Light.Ends.storeToThen (ptrBase + j) (boxBase + j * stride V boxCut : ℕ)
            ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightReportingSuffixSetup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightReportingSuffixSetup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  LightReportingSuffixSetup.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp,(subsetMask (preL j) : ℤ),(subsetMask (preR j) : ℤ),
      (boxBase+j*stride V boxCut : ℤ),result,
      Function.update ν (ptrBase+j) (boxBase+j*stride V boxCut : ℤ),?_,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases he : i = j
      · subst i; simp
      · rw [Function.update_of_ne (by omega),hkeepCall (ptrBase+i) ⟨by omega,Or.inl (by omega)⟩]
        exact hptrs i (by omega)
    · intro i hi
      by_cases he : i = j
      · subst i
        apply boxStored_of_on hnew
        intro x hx₀ hx₁
        exact Function.update_of_ne (Nat.ne_of_gt (hwriteBelow.trans_le hx₀)) _ _
      · have hij : i < j := by omega
        apply boxStored_of_on (hboxes i hij)
        intro x hx₀ hx₁
        rw [Function.update_of_ne (by omega)]
        apply hkeepCall x
        have hm := Nat.mul_le_mul_right (stride V boxCut) (show i+1 ≤ j by omega)
        change x < boxBase+i*stride V boxCut+stride V boxCut at hx₁
        constructor
        · nlinarith
        · exact Or.inl (by nlinarith)
    · intro i hi
      rw [Function.update_of_ne (by omega)]
      exact (hkeepCall i ⟨by omega,Or.inl (by omega)⟩).trans (hkeep i hi)
  case done =>
    rintro _ _ ⟨a,b,addr,r,μ',rfl,hptrs,hboxes,hkeep⟩
    refine ⟨?_,hboxes,?_,?_,hkeep⟩
    · intro i hi
      have hin : i < n := by simpa using hi
      simpa only [List.getElem_map,List.getElem_ofFn,Nat.cast_add,Nat.cast_mul] using hptrs i hin
    · exact LightSignedLeafBatch.storedThrough_of_on hstoredL (by intro i _ hi; exact hkeep i (by omega))
    · exact LightSignedLeafBatch.storedThrough_of_on hstoredR (by intro i _ hi; exact hkeep i (by omega))
  case bound =>
    rintro j _ hj _ ⟨a,b,addr,r,μ',rfl,_,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))









end ThreeSum.LightReportingSuffixCatalog

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int}
  {W V offset cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work B D d : Nat}
  (hfit : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset V) W)
  (preL preR : Nat → Finset.{0} (Fin W)) (f g : Finset.{0} (Fin W) → Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat cut W →
      @LE.le.{0} Nat instLENat boxCut V →
        @LE.le.{0} Nat instLENat stage W →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseL
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (ThreeSum.SubsetAddress.downsetCap W cut)))
              ptrBase →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseR
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (ThreeSum.SubsetAddress.downsetCap W cut)))
                ptrBase →
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inL n) ptrBase →
                @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inR n)
                    ptrBase →
                  @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ptrBase n)
                      boxBase →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                            (ThreeSum.LightReportingSuffixCatalog.stride V boxCut)))
                        maskBase →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
                            (ThreeSum.SubsetAddress.downsetCap V boxCut))
                          work →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (ThreeSum.LightPascal.tableSize W))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            lim.space →
                          @LE.le.{0} Int Int.instLEInt
                              (@Nat.cast.{0} Int instNatCastInt
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              lim.word →
                            @LE.le.{0} Int Int.instLEInt
                                (@Nat.cast.{0} Int instNatCastInt
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) V)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) stage)
                                        B)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) stage)
                                        D))))
                                lim.word →
                              (∀ (i : Nat),
                                  @LT.lt.{0} Nat instLTNat i n → @Eq.{1} Nat (@Finset.card.{0} (Fin W) (preL i)) cL) →
                                (∀ (i : Nat),
                                    @LT.lt.{0} Nat instLTNat i n → @Eq.{1} Nat (@Finset.card.{0} (Fin W) (preR i)) cR) →
                                  @LE.le.{0} Nat instLENat
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cL boxCut) cut →
                                    @LE.le.{0} Nat instLENat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cR boxCut)
                                        cut →
                                      (∀ (S : Finset.{0} (Fin W)),
                                          @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin W) S) cut →
                                            @LE.le.{0} Int Int.instLEInt
                                              (@abs.{0} Int instLatticeInt Int.instAddGroup (f S))
                                              (@Nat.cast.{0} Int instNatCastInt B)) →
                                        (∀ (S : Finset.{0} (Fin W)),
                                            @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin W) S) cut →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup (g S))
                                                (@Nat.cast.{0} Int instNatCastInt D)) →
                                          @ThreeSum.LightZetaStages.StoredThrough W μ baseL cut f W →
                                            @ThreeSum.LightZetaStages.StoredThrough W μ baseR cut g W →
                                              (∀ (i : Nat),
                                                  @LT.lt.{0} Nat instLTNat i n →
                                                    @Eq.{1} Int
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          inL i))
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (@ThreeSum.SubsetAddress.subsetMask W (preL i)))) →
                                                (∀ (i : Nat),
                                                    @LT.lt.{0} Nat instLTNat i n →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) inR i))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@ThreeSum.SubsetAddress.subsetMask W (preR i)))) →
                                                  @LE.le.{0} Nat instLENat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          d W)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                                                      lim.depth →
                                                    Light.Meets lim ThreeSum.LightReportingSuffixCatalog.program
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) d
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt boxCut)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt stage)
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cL)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt cR)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt V)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt offset)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt baseL)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt baseR)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt inL)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt inR)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt n)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    ptrBase)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      boxBase)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        (ThreeSum.LightReportingSuffixCatalog.stride
                                                                                          V boxCut))
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt maskBase)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt work)
                                                                                          (@List.nil.{0}
                                                                                            Int)))))))))))))))))))
                                                      μ (ThreeSum.LightReportingSuffixCatalog.time W V boxCut offset n)
                                                      fun (x : Int) (μ' : Nat → Int) =>
                                                      And
                                                        (Light.SegN μ' ptrBase
                                                          (@List.ofFn.{0} Nat n fun (i : Fin n) =>
                                                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) boxBase
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat) (@Fin.val n i)
                                                                (ThreeSum.LightReportingSuffixCatalog.stride V
                                                                  boxCut))))
                                                        (And
                                                          (∀ (i : Nat),
                                                            @LT.lt.{0} Nat instLTNat i n →
                                                              @ThreeSum.LightBoxStages.StoredThrough V μ'
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) boxBase
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat) i
                                                                    (ThreeSum.LightReportingSuffixCatalog.stride V
                                                                      boxCut)))
                                                                boxCut
                                                                (@ThreeSum.ReportingHostSuffix.leafWeight W V offset
                                                                  hfit f g stage (preL i) (preR i))
                                                                V)
                                                          (And
                                                            (@ThreeSum.LightZetaStages.StoredThrough W μ' baseL cut f W)
                                                            (And
                                                              (@ThreeSum.LightZetaStages.StoredThrough W μ' baseR cut g
                                                                W)
                                                              (Light.Kept μ μ' ptrBase)))) := by
  exact @ThreeSum.LightReportingSuffixCatalog.program_meets_sourceProof

#print axioms solution
