-- Prove2me | solution 1 for ThreeSum.LightSharedReportingLevels.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:48:09.599138+00:00
-- url     : https://prove2.me/submissions/dc5f6bb9-ceba-4224-a191-a9cf7cac9b10

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
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
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while
import Theorems.Thm_ThreeSum_LightSharedReportingCell_program_meets
import Theorems.Thm_ThreeSum_LightSharedReportingLoop_forSum
import Theorems.Thm_ThreeSum_LightSwitchScalar_scalar_safe
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_window
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
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







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩



















































/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































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









































/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
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
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

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





































































/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
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
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

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


/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation

open Light












theorem lookup {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body) (prefixProgram : Program) :
    (program prefixProgram P)[prefixProgram.length+p]? = some (relocate prefixProgram.length body) := by
  apply getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (prefixProgram : Program) :
    Exec lim (program prefixProgram P) d (relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (prefixProgram : Program) :
    Ends lim (program prefixProgram P) d (relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,exec he prefixProgram,hc,hq⟩

theorem meets {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (prefixProgram : Program) :
    Meets lim (program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨relocate prefixProgram.length body,lookup hbody prefixProgram,ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end

section


/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}


























theorem count_pos (h k : ℕ) : 0 < count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
































































































































end ThreeSum.LightReportingPrefixCatalog

end

section


/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout

open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000




































theorem ordered (base h J k boxCut : ℕ) :
    base ≤ pairL base h ∧ pairL base h ≤ pairR base h ∧ pairR base h ≤ stageL base h ∧
      stageL base h ≤ stageR base h k ∧ stageR base h k ≤ pointers base h k ∧
      pointers base h k ≤ boxes base h k ∧ boxes base h k ≤ masks base h J k boxCut ∧
      masks base h J k boxCut ≤ work base h J k boxCut ∧
      work base h J k boxCut ≤ finish base h J k boxCut := by
  simp only [finish,work,masks,boxes,pointers,stageR,stageL,pairR,pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    finish base h J k boxCut=base+cellSize h J k boxCut := by
  unfold cellSize finish work masks boxes pointers stageR stageL pairR pairL
  omega






theorem index_end (base h J k boxCut : ℕ) :
    index base h J k boxCut+count h k ≤ work base h J k boxCut := by
  unfold index work
  omega






theorem pair_scratch (base h J k boxCut : ℕ) :
    work base h J k boxCut+2*(512*h)+2 ≤ finish base h J k boxCut := by
  unfold finish localWidth
  omega

theorem table_scratch (base h J k boxCut : ℕ) :
    work base h J k boxCut+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤
      finish base h J k boxCut := by
  unfold finish width localWidth
  omega









































theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    levelOffset h J boxCut k ≤ levelOffset h J boxCut (k+1) := by
  rw [levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    finish (base+levelOffset h J boxCut k) h J k (boxCut k)=
      base+levelOffset h J boxCut (k+1) := by
  rw [finish_add,levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout

end

section


/-! # Retain earlier shared catalogs while appending a later metadata record -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
























theorem Entry.of_later {h J k record nextRecord low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord 5)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+5 ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

end ThreeSum.SharedReportingBankData

end

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0






















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _

theorem switchIndex_le {J j r q : ℕ} (hq : q ∈ candidates J j r) :
    switchIndex J j r ≤ q := by
  have h : (candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq

noncomputable section









































































































































































































end
end ThreeSum.Switch

end

section


/-!
# Finite scalar bounds and minimality for the executed cubic switch

These are the exact cleared integer comparisons of `Switch.switchIndex`.
No real arithmetic is executed by the eventual program.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000






theorem cubic_eq (r q : ℕ) : cubic r q=Switch.cubicNumerator r q := by
  unfold cubic Switch.cubicNumerator
  ring

theorem accepts_iff (J j r q : ℕ) :
    Switch.accepts J j r q ↔ left J j r ≤ factor J j*cubic r q := by
  have hl : left J j r=(291*J+1000*j)*r^3 := by unfold left; ring
  rw [hl,cubic_eq]
  rfl

theorem before_rejects {J j r q : ℕ}
    (hne : (Switch.candidates J j r).Nonempty) (hq : q < Switch.switchIndex J j r) :
    factor J j*cubic r q < left J j r := by
  have hb := (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1
  have hno : ¬ Switch.accepts J j r q := by
    intro h
    have hm := Switch.switchIndex_le (Switch.mem_candidates.mpr ⟨by omega,h⟩)
    omega
  rw [accepts_iff] at hno
  omega

theorem at_accepts {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    left J j r ≤ factor J j*cubic r (Switch.switchIndex J j r) :=
  (accepts_iff _ _ _ _).mp (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).2

theorem index_le_residual {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    Switch.switchIndex J j r ≤ r :=
  (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1.trans (Nat.div_le_self _ _)
















end ThreeSum.LightSwitch

end

section


/-!
# Execute the exact cubic switch in the benchmark language

The fixed procedure increases q from zero until the first accepted integer.
At every prescribed reporting depth that integer exists, including when
the residual is zero. Memory is unchanged and all scalar intermediates fit
the explicit polynomial word bound.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000













variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem frame_vars_bound (hj : j ≤ J) (hq : q ≤ r) :
    ∀ i, |(frame [(J : ℤ),j,r,q]) i| ≤ ((J+r+1001 : ℕ) : ℤ) := by
  intro i
  rcases i with _ | _ | _ | _ | i <;> simp [frame] <;> omega

theorem test_safe (hj : j ≤ J) (hq : q ≤ r)
    (hword : (word J r : ℤ) ≤ lim.word) :
    test.Safe lim ⟨frame [(J : ℤ),j,r,q],μ⟩ := by
  have hv := frame_vars_bound hj hq
  have hB : 2 ≤ J+r+1001 := by omega
  unfold test Cond.Safe
  constructor
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (((Light.Expr.op Light.Op.mul)
                      ((Light.Expr.op Light.Op.mul) (k 10)
                        ((Light.Expr.op Light.Op.sub) (v 0) (v 1)))
                      ((Light.Expr.op Light.Op.mul) (v 3)
                        ((Light.Expr.op Light.Op.add)
                          ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (k 799) (v 2))
                            (v 2))
                          ((Light.Expr.op Light.Op.mul) (v 3)
                            ((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.mul) (k 72) (v 2))
                              ((Light.Expr.op Light.Op.mul) (k 24) (v 3)))))))).cost ≤ 64))).trans hword
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (((Light.Expr.op Light.Op.mul)
                      ((Light.Expr.op Light.Op.mul)
                        ((Light.Expr.op Light.Op.mul)
                          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (k 291) (v 0))
                            ((Light.Expr.op Light.Op.mul) (k 1000) (v 1)))
                          (v 2))
                        (v 2))
                      (v 2))).cost ≤ 64))).trans hword

theorem test_holds_iff (hj : j ≤ J) :
    test.Holds ⟨frame [(J : ℤ),j,r,q],μ⟩ ↔ factor J j*cubic r q < left J j r := by
  simp only [test,Cond.Holds,Expr.val,Op.eval,frame,List.getD_cons_zero,
    List.getD_cons_succ,Nat.cast_add,Nat.cast_ofNat]
  unfold factor cubic left
  exact_mod_cast (Iff.rfl :
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r ↔
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r)

theorem meets {p : ℕ} (hp : P[p]?=some body) (hj : j ≤ J)
    (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim P p d [J,j,r] μ (time r)
      (fun result ν => result=(Switch.switchIndex J j r : ℤ) ∧ ν=μ) := by
  have hindex := index_le_residual hne
  have hbase : J+r+1001 ≤ word J r :=
    Nat.le_self_pow (by decide : (64 : ℕ) ≠ 0) _
  have hlinear : ((J+r+1001 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hbase).trans hword
  apply Meets.of_body hp
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
  refine Ends.next (50*Switch.switchIndex J j r+60) (Ends.whileBlock
    (fun i σ => σ=⟨frame [(J : ℤ),j,r,i],μ⟩)
    (Switch.switchIndex J j r) (by simp) ?round ?done (by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, test]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [test] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))))
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, test]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [test] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))))
  case round =>
    rintro i _ hi rfl
    have hle : i ≤ r := by omega
    refine ⟨test_safe hj hle hword,
      (test_holds_iff hj).mpr (before_rejects hne hi),by (((try have := Light.Std.space_le (by assumption)));
                                                           ((try have := Light.Std.const_le (by assumption)));
                                                           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),?_⟩
    simp [update_frame_setLocal]
  case done =>
    rintro _ rfl
    refine ⟨test_safe hj hindex hword,?_,?_⟩
    · rw [test_holds_iff hj]
      exact not_lt_of_ge (at_accepts hne)
    · focus
         ((((first
                 | refine Light.Ends.seqSelf ?_
                 | refine Light.Ends.skipLast ?_));
             (repeat
                 with_unfolding_none
                   first
                   | refine Light.Ends.seqAssoc ?_
                   | refine Light.Ends.skipThen ?_)));
         (refine Light.Ends.setToThen (Switch.switchIndex J j r) ?_ ?_ ?_);
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
      exact ⟨rfl,rfl⟩



theorem program_meets (hj : j ≤ J) (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim program 0 d [J,j,r] μ (time r)
      (fun result ν => result=(Switch.switchIndex J j r : ℤ) ∧ ν=μ) :=
  meets rfl hj hne hword











end ThreeSum.LightSwitch

end

section


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000













theorem level_le {J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold LightSwitchDepth.depth at hk
  omega

















theorem switch_le {h J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) :
    switch h J k ≤ residual h J k :=
  LightSwitch.index_le_residual (candidates_nonempty hk)

theorem boxCut_le (h J k : ℕ) : boxCut h J k ≤ residual h J k := Nat.sub_le _ _

theorem residual_le_width (h J k : ℕ) : residual h J k ≤ (J-k)*(512*h) := by
  unfold residual
  nlinarith

theorem pre_cut {h J k : ℕ} (hk : k ≤ J) : k*h+boxCut h J k ≤ 2*h*J := by
  have hc := boxCut_le h J k
  have hd := Nat.sub_add_cancel hk
  unfold residual at hc
  nlinarith

theorem count_zero (h : ℕ) : count h 0=1 := by simp [count]
theorem count_succ (h k : ℕ) : count h (k+1)=count h k*localPairs h := by
  simp only [count,localPairs,localWidth,pow_succ]
theorem span_zero (h : ℕ) : prefixSpan h 0=2 := by
  simp [prefixSpan,LightRadixKeys.offset,count]
theorem span_succ (h k : ℕ) : prefixSpan h (k+1)=prefixSpan h k+1+count h (k+1) := by
  unfold prefixSpan
  rw [LightRadixKeys.offset]
  change LightRadixKeys.offset (localPairs h) k+1+count h k+1+count h (k+1)=_
  omega

theorem count_mono (h : ℕ) : Monotone (count h) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by
    have hh := count_pos h 1
    simpa only [count,pow_one] using hh) hij

theorem span_mono (h : ℕ) : Monotone (prefixSpan h) :=
  monotone_nat_of_le_succ (fun k => by rw [span_succ]; omega)

theorem baseAt_zero (base h J : ℕ) : baseAt base h J 0=base := rfl
theorem baseAt_mono (base h J : ℕ) : Monotone (baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (levelOffset_mono h J (boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) :=
  finish_level base h J k (boxCut h J)

theorem catalog_low (base h J k : ℕ) :
    base ≤ (catalogAt base h J k).indexBase ∧
    base ≤ (catalogAt base h J k).ptrBase ∧
    base ≤ (catalogAt base h J k).boxBase := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hb : base ≤ baseAt base h J k := Nat.le_add_right _ _
  dsimp only [catalogAt,catalog,index]
  omega

theorem catalog_end (base h J k : ℕ) :
    (catalogAt base h J k).indexBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).ptrBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).boxBase+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k) ≤ baseAt base h J (k+1) := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hi := index_end (baseAt base h J k) h J k (boxCut h J k)
  have hp : pointers (baseAt base h J k) h k+count h k=boxes (baseAt base h J k) h k := rfl
  have hm : boxes (baseAt base h J k) h k+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k)=masks (baseAt base h J k) h J k (boxCut h J k) := rfl
  rw [← finish_baseAt]
  dsimp only [catalogAt,catalog]
  omega

theorem Built.empty (μ : ℕ → ℤ) (record base h J : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Built μ record base h J 0 f g := by
  intro k hk
  omega

theorem Built.append {μ ν : ℕ → ℤ} {record base h J i : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Built μ record base h J i f g)
    (hi : i ≤ J)
    (Hnew : Entry ν (record+5*i) (catalogAt base h J i) hi f g)
    (hkeep : KeptBut μ ν (baseAt base h J i) (record+5*i) 5)
    (hrecord : record+5*i+5 ≤ base) : Built ν record base h J (i+1) f g := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨hjJ,Hj⟩ := H j hj
    have hlow := catalog_low base h J j
    have hend := catalog_end base h J j
    have hbefore := baseAt_mono base h J (show j+1 ≤ i by omega)
    refine ⟨hjJ,Hj.of_later hkeep (by omega) hrecord
      (Nat.le_add_right _ _) hlow.1 hlow.2.1 hlow.2.2
      (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
  · exact ⟨hi,Hnew⟩

end ThreeSum.SharedReportingBankLevels

end

section


/-!
# Construct every level once for one occurrence and independent source bands

The loop executes the cubic switch, maintains the exact prefix count and
prefix-array span, and appends one compact catalog per level. Its budget is
the sum of the actual level budgets. Five-cell metadata records are
contiguous; completed payloads remain immutable.
-/

namespace ThreeSum.LightSharedReportingLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000















































theorem program_meets_sourceProof {lim : Limits} {μ : ℕ → ℤ}
    {record base h J K baseL baseR cellL cellR B D d : ℕ}
    (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ LightSwitchDepth.depth J+1)
    (hrecords : record+5*K ≤ base)
    (hcellL : cellL < record) (hcellR : cellR < record)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (R : Resources lim base h J K B D d)
    (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(512*h))) :
    Meets lim program 64 d
      [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base] μ (time h J K)
      (fun result ν => result=(baseAt base h J K : ℤ) ∧
        Built ν record base h J K f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)) := by
  have hstate := R.state
  have hspace := R.space
  have hdepth := R.widthDepth
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hKWord : (K : ℤ) ≤ lim.word := by omega
  have hJWord : (J : ℤ) ≤ lim.word := by omega
  have hconstants : (512 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body (p := 64) (by rfl : program[64]?=some (body 63 62))
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
    (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (base : ℕ) ?_ ?_ ?_);
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
  refine Ends.pieceThen (LightSharedReportingLoop.forSum
    (T := (∑ i ∈ Finset.range K, (roundTime h J i+8))+6)
    (Q := Inv μ record base h J K cellL cellR K f g)
    (Inv μ record base h J K cellL cellR · f g) K (roundTime h J)
    ?start ?round ?done ?bound hKWord (by
      simp only [Expr.cost]
      have hs : (∑ i ∈ Finset.range K, (1+roundTime h J i+7))=
          ∑ i ∈ Finset.range K, (roundTime h J i+8) := by
        apply Finset.sum_congr rfl
        intro i hi
        omega
      omega)) ?finish
  case start =>
    refine ⟨0,0,0,μ,?_,Built.empty _ _ _ _ _ _ _,SameOn.refl,fun _ _ => rfl⟩
    simp only [SharedReportingBankLevels.count_zero,span_zero,baseAt_zero]
    simp [update_frame_setLocal]
    exact (frame_append_zeros [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base,1,2,base,0] 3).symm
  case round =>
    rintro i _ hi _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    have hiDepth : i ≤ LightSwitchDepth.depth J := by omega
    have hiJ := level_le hiDepth
    have hnext := baseAt_mono base h J (show i+1 ≤ K by omega)
    have hcellSpace : finish (baseAt base h J i) h J i (boxCut h J i) ≤ lim.space := by
      rw [finish_baseAt]
      exact hnext.trans hspace
    have hbefore := baseAt_mono base h J (show i ≤ K by omega)
    have hcurrent : baseAt base h J i ≤ lim.space := hbefore.trans hspace
    have hlocalSpace := (pair_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hwidthSpace := (table_scratch (baseAt base h J i) h J i (boxCut h J i)).trans hcellSpace
    have hW : J*(512*h) ≤ lim.space := by omega
    have hL : 512*h ≤ lim.space := by omega
    have hV : (J-i)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hrV := residual_le_width h J i
    have hrNat : residual h J i ≤ lim.space := by omega
    have hrWord : (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) ≤ lim.word := by
      simpa only [SharedReportingBankLevels.residual,Nat.cast_mul,Nat.cast_sub hiJ,Nat.cast_ofNat] using
        (Int.ofNat_le.mpr hrNat).trans hw
    have hrNZ : (0 : ℤ) ≤ (2 : ℤ)*(h : ℤ)*((J : ℤ)-(i : ℤ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (Int.ofNat_le.mpr hiJ))
    have hN := count_mono h (show i+1 ≤ K by omega)
    have hspan := span_mono h (show i+1 ≤ K by omega)
    have hprod : (count h i : ℤ)*(localPairs h : ℤ)=(count h (i+1) : ℤ) := by
      rw [SharedReportingBankLevels.count_succ,Nat.cast_mul]
    have hprodNZ : (0 : ℤ) ≤ (count h i : ℤ)*(localPairs h : ℤ) := by positivity
    have hspanEq := span_succ h i
    have hrecord : record+5*i+5 ≤ baseAt base h J i := by
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      omega
    unfold roundTime
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (residual h J i : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  SharedReportingBankLevels.residual, Nat.cast_sub hiJ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [SharedReportingBankLevels.residual, Nat.cast_sub hiJ] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  SharedReportingBankLevels.residual, Nat.cast_sub hiJ] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hs := (ReportingHostRelocation.meets
      (LightSwitch.program_meets (μ := ν) (d := d+1) hiJ (candidates_nonempty hiDepth) (R.switch i hi))
      LightSharedReportingCell.program).append [body 63 62]
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
        | refine Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
        | refine Light.Ends.callToThen hs ?_ ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  SharedReportingBankLevels.residual]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [SharedReportingBankLevels.residual] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  SharedReportingBankLevels.residual] <;>
                omega)));
      (on_goal -1 =>
          ((rintro actual νt ⟨hactual, hmem⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    subst νt
    have hswitch := switch_le (h := h) hiDepth
    change Switch.switchIndex J i (residual h J i) ≤ residual h J i at hswitch
    have htWord : (switch h J i : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hswitch.trans hrNat)).trans hw
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (boxCut h J i : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, boxCut,
                  switch, hactual]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [boxCut, switch, hactual] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, boxCut, switch, hactual] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    have hsourceL : LightZetaStages.StoredThrough ν baseL (2*h*J) f (J*(512*h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL
        (by intro a _ ha; exact kept a (by omega))
    have hsourceR : LightZetaStages.StoredThrough ν baseR (2*h*J) g (J*(512*h)) :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR
        (by intro a _ ha; exact kept a (by omega))
    have hreadL : ν cellL=(baseL : ℤ) := (kept cellL hcellL).trans hleftRead
    have hreadR : ν cellR=(baseR : ℤ) := (kept cellR hcellR).trans hrightRead
    have hc := ((LightSharedReportingCell.program_meets (μ := ν) (d := d+1)
      (k := i) (boxCut := boxCut h J i) (baseL := baseL) (baseR := baseR)
      (cellL := cellL) (cellR := cellR) (free := baseAt base h J i) (rec := record+5*i)
      (B := B) (D := D) (t := switch h J i) hiJ f g hw hconstants hJWord
      ((boxCut_le h J i).trans hrV) (by omega) (by omega) (by omega) (by omega) hrecord
      hcellSpace R.powers (R.keys i hi) R.width (R.index i hi) (R.values i hi) htWord
      (pre_cut hiJ) hf hg hreadL hreadR hsourceL hsourceR
      (by have hh := R.pairDepth; omega) (by have hh := R.widthDepth; omega)
      (by have hh := R.sortDepth i hi; omega)).append
        (LightSwitch.program.map (ReportingHostRelocation.relocate LightSharedReportingCell.program.length))).append
          [body 63 62]
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
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hactual,
                  switch]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hactual, switch] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hactual, switch] <;>
                omega)));
      (on_goal -1 =>
          ((rintro next ν₁ ⟨hnextFree, hentry, _, _, hkeepCell⟩);
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
      (refine Light.Ends.setToThen (count h (i + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  SharedReportingBankLevels.count_succ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [SharedReportingBankLevels.count_succ] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  SharedReportingBankLevels.count_succ] <;>
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
      (refine Light.Ends.setToThen (prefixSpan h (i + 1) : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  span_succ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [span_succ] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, span_succ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨by simp,residual h J i,switch h J i,boxCut h J i,ν₁,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal,hnextFree,finish_baseAt,hactual,switch]
    · exact built.append hiJ hentry hkeepCell (by omega)
    · intro a ha
      exact (hkeepCell a ⟨by omega,Or.inl (by omega)⟩).trans (kept a ha)
    · intro a ⟨ha,houtside⟩
      have hb : base ≤ baseAt base h J i := Nat.le_add_right _ _
      exact (hkeepCell a ⟨by omega,by rcases houtside with h | h <;> omega⟩).trans
        (keptBlock a ⟨ha,houtside⟩)
  case done =>
    rintro _ _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    exact ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
  case bound =>
    rintro i _ _ _ ⟨r,t,cut,ν,rfl,_,_,_⟩
    (((try have := Light.Std.space_le (by assumption)));
      ((try have := Light.Std.const_le (by assumption)));
      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
  case finish =>
    rintro _ ⟨r,t,cut,ν,rfl,built,kept,keptBlock⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (baseAt base h J K : ℕ) ?_ ?_ ?_);
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
    exact ⟨rfl,built,kept,keptBlock⟩

end ThreeSum.LightSharedReportingLevels

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {record base h J K baseL baseR cellL cellR B D d : Nat}
  (f g :
    Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))) →
      Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat K
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightSwitchDepth.depth J)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K))
          base →
        @LT.lt.{0} Nat instLTNat cellL record →
          @LT.lt.{0} Nat instLTNat cellR record →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseL
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (ThreeSum.SubsetAddress.downsetCap
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                        J))))
                record →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) baseR
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (ThreeSum.SubsetAddress.downsetCap
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                          J))))
                  record →
                ThreeSum.LightSharedReportingLevels.Resources lim base h J K B D d →
                  (∀
                      (S :
                        Finset.{0}
                          (Fin
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
                      @LE.le.{0} Nat instLENat
                          (@Finset.card.{0}
                            (Fin
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                            S)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                            J) →
                        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f S))
                          (@Nat.cast.{0} Int instNatCastInt B)) →
                    (∀
                        (S :
                          Finset.{0}
                            (Fin
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
                        @LE.le.{0} Nat instLENat
                            (@Finset.card.{0}
                              (Fin
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                              S)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                              J) →
                          @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (g S))
                            (@Nat.cast.{0} Int instNatCastInt D)) →
                      @Eq.{1} Int (μ cellL) (@Nat.cast.{0} Int instNatCastInt baseL) →
                        @Eq.{1} Int (μ cellR) (@Nat.cast.{0} Int instNatCastInt baseR) →
                          @ThreeSum.LightZetaStages.StoredThrough
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                              μ baseL
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                                J)
                              f
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
                            @ThreeSum.LightZetaStages.StoredThrough
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                μ baseR
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                                  J)
                                g
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
                              Light.Meets lim ThreeSum.LightSharedReportingLevels.program
                                (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) d
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cellL)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cellR)
                                          (@List.cons.{0} Int
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (ThreeSum.SharedReportingBankLayout.localChoose h))
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (ThreeSum.SharedReportingBankLayout.localPairs h))
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt record)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                                  (@List.nil.{0} Int))))))))))
                                μ (ThreeSum.LightSharedReportingLevels.time h J K) fun (result : Int) (ν : Nat → Int) =>
                                And
                                  (@Eq.{1} Int result
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (ThreeSum.SharedReportingBankLevels.baseAt base h J K)))
                                  (And (ThreeSum.SharedReportingBankLevels.Built ν record base h J K f g)
                                    (And (Light.Kept μ ν record)
                                      (Light.KeptBut μ ν base record
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K)))) := by
  exact @ThreeSum.LightSharedReportingLevels.program_meets_sourceProof

#print axioms solution
