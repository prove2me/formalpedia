-- Prove2me | solution 1 for ThreeSum.LightQueryBox.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:37:54.426983+00:00
-- url     : https://prove2.me/submissions/4d4fe86c-af94-4ff4-8d8e-13d06f940013

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Finset.Max
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
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_BoxStages_partialZeta_eq_boxSum
import Theorems.Thm_ThreeSum_LightMaskMinimum_meets
import Theorems.Thm_ThreeSum_LightStageLookup_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BoxStages
end ThreeSum.BoxStages
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
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
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes

open scoped BigOperators

variable {α : Type*} [LinearOrder α]








































































theorem queryFree_eq_filter_min (q u : Finset α) (hu : u.Nonempty) :
    queryFree q u = (q \ u).filter (fun x => x < u.min' hu) := by
  ext x
  simp only [queryFree, Finset.mem_filter]
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, ho _ (Finset.min'_mem u hu)⟩
  · rintro ⟨hx, ho⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact ho.trans_le (Finset.min'_le u y hy)





































































/-! ## Canonical free prefixes and the finite preprocessing family -/








































































































































































/-! ## The exact addition recurrence and query sum -/




































































































































































































/-! ## Number of query accesses -/
































































end ThreeSum.SparseBoxes

end

section


/-!
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset



@[simp] theorem mem_prefix {L j : ℕ} (a : Fin L) : a ∈ initialCoords L j ↔ a.val < j := by
  simp [initialCoords]





@[simp] theorem prefix_all (L : ℕ) : initialCoords L L = univ := by
  ext a
  simp only [mem_prefix,mem_univ,iff_true]
  exact a.isLt









































































































theorem stageValue_eq_boxSum {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (j : ℕ) (flags : Finset (Fin L)) :
    stageValue weight j flags = SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight :=
  partialZeta_eq_boxSum weight flags (initialCoords L j)

theorem queryFree_prefix {L : ℕ} (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.queryFree q u = (q \ u) ∩ initialCoords L (u.min' hu).val := by
  rw [SparseBoxes.queryFree_eq_filter_min q u hu]
  ext a
  simp only [mem_filter,mem_inter,mem_prefix]
  rfl

theorem query_box_stage {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight =
      stageValue weight (u.min' hu).val (q \ u) := by
  rw [queryFree_prefix q u hu,stageValue_eq_boxSum]

end ThreeSum.BoxStages

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







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩
















































































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

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
  Ends.next T₁ (h.mono le_rfl rest) hT





































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
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
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

























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

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

end
end

section


/-!
# Building and retaining every compact prefix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for canonical
sparse-box queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightBoxStages

open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}


















































































































































































theorem stored_box_lookup {μ : ℕ → ℤ} {L cut base j : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L) (hj : j ≤ L)
    (flags : Finset (Fin L)) (hflags : flags.card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank flags) =
      SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight := by
  rw [h j hj flags hflags]
  exact stageValue_eq_boxSum weight j flags

theorem stored_query_box {μ : ℕ → ℤ} {L cut base : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L)
    (q u : Finset (Fin L)) (hu : u.Nonempty) (hflags : (q \ u).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) (u.min' hu).val+subsetRank (q \ u)) =
      SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight := by
  rw [h (u.min' hu).val (Nat.le_of_lt (u.min' hu).isLt) (q \ u) hflags]
  exact (query_box_stage weight q u hu).symm






















end ThreeSum.LightBoxStages

end

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]

@[simp] theorem subsetMask_empty (L : ℕ) : subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [subsetMask_sum]

theorem subsetMask_eq_zero_iff {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    exact subsetMask_injective L (h.trans (subsetMask_empty L).symm)
  · rintro rfl
    exact subsetMask_empty L




























theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by
  have h := subsetMask_union_sdiff Q U hU
  have hz : (subsetMask U : ℤ)+(subsetMask (Q \ U) : ℤ) = (subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

end

section


/-!
# Executing a canonical sparse-query box

Given valid masks `U ⊆ Q`, the program subtracts their masks and
cardinalities, computes the least missing coordinate itself, computes
the compact stage address, and reads the signed box sum. The empty
missing set uses the final prefix stage. No address or minimum is
provided as advice.
-/

namespace ThreeSum.LightQueryBox

open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}












theorem meets_sourceProof
    {pMain pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        Kept μ μ' work) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hpow : (2^L : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpowZ : ((2^L : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hpow : ((2^L : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword₀
  have hcardle := Finset.card_le_card hU
  have hcardDiff := Finset.card_sdiff_of_subset hU
  have hcard : (Q.card : ℤ)-(U.card : ℤ) = ((Q \ U).card : ℤ) := by omega
  have hmask := subsetMask_sdiff_int Q U hU
  have hmaskBound : (subsetMask (Q \ U) : ℤ) < ((2^L : ℕ) : ℤ) := by
    exact_mod_cast (subsetMask_isMask (Q \ U)).1
  have hmaskNonneg : (0 : ℤ) ≤ subsetMask (Q \ U) := Int.natCast_nonneg _
  have hr := subsetRank_lt hflags
  have haddr (j : ℕ) (hj : j ≤ L) : LightStageLookup.readAddr cut base j (Q \ U) < work := by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
    unfold LightStageLookup.readAddr
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  apply Meets.of_body hmain
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
    (refine Light.Ends.setToThen ((Q \ U).card : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcard,
                LightMaskMinimum.time, LightStageLookup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcard, LightMaskMinimum.time, LightStageLookup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcard,
                LightMaskMinimum.time, LightStageLookup.time] <;>
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
    (refine Light.Ends.setToThen (subsetMask (Q \ U) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hmask,
                LightMaskMinimum.time, LightStageLookup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hmask, LightMaskMinimum.time, LightStageLookup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hmask,
                LightMaskMinimum.time, LightStageLookup.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.pieceThen (Ends.iteLast
    (T := LightMaskMinimum.time L+20)
    (Q := fun σ => ∃ (j : ℕ), j ≤ L ∧
      σ.loc = frame (setLocal (setLocal (setLocal
        [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work]
        8 ((Q \ U).card : ℤ)) 9 (subsetMask (Q \ U) : ℤ)) 10 (j : ℤ)) ∧
      Kept μ σ.mem work ∧
      σ.mem (LightStageLookup.readAddr cut base j (Q \ U)) =
        SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight)
    ?zero ?nonzero (by (((try have := Light.Std.space_le (by assumption)));
                         ((try have := Light.Std.const_le (by assumption)));
                         (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT := by first
                                                                                              |
                                                                                                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                                                                                                      LightMaskMinimum.time]);
                                                                                                  (first
                                                                                                    | omega
                                                                                                    | ((ring_nf); (omega))))
                                                                                              | omega
                                                                                              |
                                                                                                (simp [LightMaskMinimum.time] <;>
                                                                                                    first
                                                                                                    | omega
                                                                                                    | ((ring_nf); (omega)))))
    ?after (hT := by first
                     |
                       ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                             LightMaskMinimum.time, LightStageLookup.time]);
                         (first
                           | omega
                           | ((ring_nf); (omega))))
                     | omega
                     |
                       (simp [LightMaskMinimum.time, LightStageLookup.time] <;>
                           first
                           | omega
                           | ((ring_nf); (omega))))
  case zero =>
    intro hz
    have hz' : subsetMask U = 0 := by exact_mod_cast (by simpa using hz : (subsetMask U : ℤ) = 0)
    have hUempty := (subsetMask_eq_zero_iff U).mp hz'
    have hread : μ (LightStageLookup.readAddr cut base L (Q \ U)) =
        SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by
      have hh := LightBoxStages.stored_box_lookup hstored le_rfl (Q \ U) hflags
      simpa [LightStageLookup.readAddr,LightBoxStages.stageBase,SparseBoxes.queryFree,hUempty] using hh
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightMaskMinimum.time, LightStageLookup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightMaskMinimum.time, LightStageLookup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, LightMaskMinimum.time,
                  LightStageLookup.time] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    exact ⟨L,le_rfl,rfl,SameOn.refl,hread⟩
  case nonzero =>
    intro hz
    have hUpos : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      apply hz
      simp [he,subsetMask_empty]
    have hm := LightMaskMinimum.meets (d := d+1) (μ := μ) (work := work)
      hMinimum C.powers hErase U hUpos
      hw (by omega) hword₀ (by omega)
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
        | refine Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hm ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightMaskMinimum.time, LightStageLookup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightMaskMinimum.time, LightStageLookup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, LightMaskMinimum.time,
                  LightStageLookup.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro smallest μ₁ ⟨hsmallest, hminKept⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨(U.min' hUpos).val,Nat.le_of_lt (U.min' hUpos).isLt,?_,hminKept,?_⟩
    · simp only [hsmallest]
    · have hh := LightBoxStages.stored_query_box hstored Q U hUpos hflags
      exact (hminKept _ (haddr _ (Nat.le_of_lt (U.min' hUpos).isLt))).trans hh
  case after =>
    rintro σ ⟨j,hj,hloc,hkept,hread⟩
    rcases σ with ⟨loc,μ'⟩
    simp only at hloc hkept hread
    subst loc
    have hc := LightStageLookup.meets (d := d+1) hLookup hSize hAddress C hOffset
      (Q \ U) (SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight)
      hw hcut hdata hspace hword hflags hj hread (by omega)
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
        | refine Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hc ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  LightMaskMinimum.time, LightStageLookup.time]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [LightMaskMinimum.time, LightStageLookup.time] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, LightMaskMinimum.time,
                  LightStageLookup.time] <;>
                omega)));
      (on_goal -1 =>
          ((rintro res μ₁ ⟨hres, hnewKept⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    exact ⟨hres,hkept.trans hnewKept⟩
































end ThreeSum.LightQueryBox

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program}
  {pMain pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightQueryBox.body pMinimum pLookup)) →
    @Eq.{1} (Option.{0} Light.Stmt)
        (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
          (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
          (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMinimum)
        (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskMinimum.body pPowers pErase)) →
      @Eq.{1} (Option.{0} Light.Stmt)
          (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
            (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
            (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLookup)
          (@Option.some.{0} Light.Stmt (ThreeSum.LightStageLookup.body pSize pAddress)) →
        @Eq.{1} (Option.{0} Light.Stmt)
            (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
              (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
              (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSize)
            (@Option.some.{0} Light.Stmt (ThreeSum.LightDownsetSize.body pSetup pOffset)) →
          @Eq.{1} (Option.{0} Light.Stmt)
              (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pAddress)
              (@Option.some.{0} Light.Stmt (ThreeSum.LightDownsetAddress.body pSetup pOffset)) →
            ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank →
              @Eq.{1} (Option.{0} Light.Stmt)
                  (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                    (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                    (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pOffset)
                  (@Option.some.{0} Light.Stmt ThreeSum.LightSubsetOffset.body) →
                @Eq.{1} (Option.{0} Light.Stmt)
                    (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
                      (fun (as : List.{0} Light.Stmt) (i : Nat) =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
                      (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
                    (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)) →
                  ∀ {μ : Nat → Int} {L cut base work d : Nat} (Q U : Finset.{0} (Fin L))
                    (weight : Finset.{0} (Fin L) → Int),
                    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
                      @LE.le.{0} Nat instLENat cut L →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (ThreeSum.SubsetAddress.downsetCap L cut)))
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
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                lim.word →
                              @LE.le.{0} (Finset.{0} (Fin L))
                                  (@Preorder.toLE.{0} (Finset.{0} (Fin L))
                                    (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L))
                                      (@Finset.instPartialOrder.{0} (Fin L))))
                                  U Q →
                                @LE.le.{0} Nat instLENat
                                    (@Finset.card.{0} (Fin L)
                                      (@SDiff.sdiff.{0} (Finset.{0} (Fin L))
                                        (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U))
                                    cut →
                                  @ThreeSum.LightBoxStages.StoredThrough L μ base cut weight L →
                                    @LE.le.{0} Nat instLENat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                        lim.depth →
                                      Light.Meets lim P pMain d
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin L) Q))
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (@ThreeSum.SubsetAddress.subsetMask L Q))
                                                (@List.cons.{0} Int
                                                  (@Nat.cast.{0} Int instNatCastInt (@Finset.card.{0} (Fin L) U))
                                                  (@List.cons.{0} Int
                                                    (@Nat.cast.{0} Int instNatCastInt
                                                      (@ThreeSum.SubsetAddress.subsetMask L U))
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                                        (@List.nil.{0} Int)))))))))
                                        μ (ThreeSum.LightQueryBox.time L) fun (r : Int) (μ' : Nat → Int) =>
                                        And
                                          (@Eq.{1} Int r
                                            (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L)
                                              (@SDiff.sdiff.{0} (Finset.{0} (Fin L))
                                                (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U)
                                              (@ThreeSum.SparseBoxes.queryFree.{0} (Fin L) (@Fin.instLinearOrder L) Q U)
                                              weight))
                                          (Light.Kept μ μ' work) := by
  exact @ThreeSum.LightQueryBox.meets_sourceProof

#print axioms solution
