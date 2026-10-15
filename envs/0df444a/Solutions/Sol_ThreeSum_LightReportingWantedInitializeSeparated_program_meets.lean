-- Prove2me | solution 1 for ThreeSum.LightReportingWantedInitializeSeparated.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:23:39.810038+00:00
-- url     : https://prove2.me/submissions/2b4e1715-c03a-4e92-b9b0-5be777316530

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum_LightBlockMasks_meets
import Theorems.Thm_ThreeSum_LightReportingInitializeStored_program_meets
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Stored_of_kept
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingWantedInitialize
end ThreeSum.LightReportingWantedInitialize
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
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


/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators
































































@[simp] theorem packedMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (packedMasks rows).length = J := by simp [packedMasks]






end ThreeSum.BlockMaskLayout

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

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl




















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

end
end

section


/-!
# Packing physical block masks into global row-major coordinates

The fixed program builds a power table, scales every input row mask by its
block position, writes the global row masks, and returns their union mask.
Only linear scans and polynomial scratch are used.
-/

namespace ThreeSum.LightBlockMasks

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout

variable {lim : Limits} {P : Program}



















































































































































theorem program_meets {μ : ℕ → ℤ} {J L src dst work d : ℕ} (rows : Fin J → Finset (Fin L))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+J ≤ work) (hdst : dst+J ≤ work) (hsep : Apart src J dst J)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : SegN μ src (rawMasks rows)) (hd : d+1 ≤ lim.depth) :
    Meets lim program 0 d [J,L,src,dst,work] μ (time J L)
      (fun r μ' => r = (subsetMask (indexSet (flat rows)) : ℤ) ∧
        SegN μ' dst (packedMasks rows) ∧ KeptBut μ μ' work dst J) :=
  meets rfl rfl rows hw hsrc hdst hsep hspace hword hread hd





end ThreeSum.LightBlockMasks

end

section


/-!
# Actual cumulative mass guard before expensive reporting

The root header is the actual Initialize output, whose third cell contains
the queried raw mass. This procedure adds that cell to the retained running
counter and returns one exactly when the computed threshold is exceeded.
It changes only the counter cell.
-/

namespace ThreeSum.LightDenseGuard

open Light








variable {lim : Limits} {P : Program} {μ : ℕ→ℤ}
  {counter root old mass threshold d : ℕ}

theorem meets {p : ℕ} (hp : P[p]?=some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    Meets lim P p d [counter,root,threshold] μ time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ SameOutside μ ν counter 1) := by
  have hmassZ : μ (((root : ℤ)+2).toNat)=(mass : ℤ) := by
    rw [show ((root : ℤ)+2).toNat=root+2 by omega]
    exact hmass
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
    (refine Light.Ends.setToThen (old + mass : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread,
                hmass, hmassZ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hread, hmass, hmassZ] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hread, hmass, hmassZ] <;>
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
    (refine Light.Ends.storeToThen counter (old + mass : ℕ) ?_ ?_ ?_);
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
        Light.Ends.iteIffThen (threshold < old + mass) (fun hyes => ?_)
          (fun hno => ?_) ?_ ?_);
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
  · focus
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
    exact ⟨by simp [hyes],by simp,by ((try refine Light.SameOn.cell ?_); (intro apspMacro_35423_0 apspMacro_35423_1);
                                         (first
                                           |
                                             ((((repeat
                                                       (((with_reducible
                                                               rename Light.SameOn _ _ _ => apspMacro_35423_2));
                                                         ((try
                                                               have :=
                                                                 apspMacro_35423_2 apspMacro_35423_0 (by omega)));
                                                         (revert apspMacro_35423_2)));
                                                   (intros);
                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                               (omega))
                                           |
                                             ((simp [] at apspMacro_35423_1);
                                               (((repeat
                                                       (((with_reducible
                                                               rename Light.SameOn _ _ _ => apspMacro_35423_3));
                                                         ((try
                                                               have :=
                                                                 apspMacro_35423_3 apspMacro_35423_0 (by omega)));
                                                         (revert apspMacro_35423_3)));
                                                   (intros);
                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                               (omega))
                                           |
                                             ((((repeat
                                                       (((with_reducible
                                                               rename Light.SameOn _ _ _ => apspMacro_35423_4));
                                                         ((try
                                                               have :=
                                                                 apspMacro_35423_4 apspMacro_35423_0 (by omega)));
                                                         (revert apspMacro_35423_4)));
                                                   (intros);
                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                               (fail
                                                   "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                             its condition K x does not follow from the hypotheses."))))⟩
  · focus
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
    exact ⟨by simp [hno],by simp,by ((try refine Light.SameOn.cell ?_); (intro apspMacro_35500_0 apspMacro_35500_1);
                                        (first
                                          |
                                            ((((repeat
                                                      (((with_reducible
                                                              rename Light.SameOn _ _ _ => apspMacro_35500_2));
                                                        ((try
                                                              have :=
                                                                apspMacro_35500_2 apspMacro_35500_0 (by omega)));
                                                        (revert apspMacro_35500_2)));
                                                  (intros);
                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                              (omega))
                                          |
                                            ((simp [] at apspMacro_35500_1);
                                              (((repeat
                                                      (((with_reducible
                                                              rename Light.SameOn _ _ _ => apspMacro_35500_3));
                                                        ((try
                                                              have :=
                                                                apspMacro_35500_3 apspMacro_35500_0 (by omega)));
                                                        (revert apspMacro_35500_3)));
                                                  (intros);
                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                              (omega))
                                          |
                                            ((((repeat
                                                      (((with_reducible
                                                              rename Light.SameOn _ _ _ => apspMacro_35500_4));
                                                        ((try
                                                              have :=
                                                                apspMacro_35500_4 apspMacro_35500_0 (by omega)));
                                                        (revert apspMacro_35500_4)));
                                                  (intros);
                                                  (try simp only [Function.update_apply, Light.wrote] at *)));
                                              (fail
                                                  "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                            its condition K x does not follow from the hypotheses."))))⟩



theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word)
    (hcounter : counter+1 ≤ lim.space) (hroot : root+3 ≤ lim.space)
    (hword : ((old+mass+threshold+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : μ counter=(old : ℤ)) (hmass : μ (root+2)=(mass : ℤ)) :
    Meets lim program 0 d [counter,root,threshold] μ time
      (fun result ν => result=(if threshold < old+mass then 1 else 0 : ℤ) ∧
        ν counter=((old+mass : ℕ) : ℤ) ∧ SameOutside μ ν counter 1) :=
  meets rfl hw hcounter hroot hword hread hmass

end ThreeSum.LightDenseGuard

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
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false













variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































theorem Bounds.mono {h J k baseL baseR stop stop' : ℕ} {D : Catalog}
    (H : Bounds h J k D baseL baseR stop) (hle : stop≤stop') :
    Bounds h J k D baseL baseR stop' :=
  ⟨H.left.trans hle,H.right.trans hle,H.index.trans hle,H.pointers.trans hle,H.boxes.trans hle⟩

theorem Sources.of_kept {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Sources μ pMod shift B C b c q baseL baseR) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Sources ν pMod shift B C b c q baseL baseR := by
  constructor
  · exact LightSignedLeafBatch.storedThrough_of_on H.left
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.left))
  · exact LightSignedLeafBatch.storedThrough_of_on H.right
      (by intro i _ hi; exact hkeep i (hi.trans_le HB.right))











































end ThreeSum.ReportingHostLevelData

end

section


/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting LightBlockQuery ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false





























@[simp] theorem query_zero {J L : ℕ} (Q : Fin J→Finset (Fin L)) :
    querySet 0 Q=indexSet (flat Q) := by
  simp [querySet,remaining,prefixIndices,flat]

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



















































































end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# Executed wanted-mask packing, root query, and cumulative guard

The program packs the decoded original query rows, initializes the actual
root frontier using persistent catalogs, and updates the running mass
counter before any proportional traversal. Its Boolean result is exactly
the actual threshold comparison. The global guard-soundness theorem can
therefore certify this early branch on the original owner domain.
-/

namespace ThreeSum.LightReportingWantedInitialize

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false
















variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem frontier_of_above {μ ν : ℕ→ℤ} {h J root cap k : ℕ}
    {I : Finset (RawItem h J α β γ)} {w : Wanted h J α}
    (H : At μ I w root cap k) (hkeep : ∀ i, root ≤ i → ν i=μ i) : At ν I w root cap k := by
  constructor
  · exact (hkeep _ (by unfold slot; omega)).trans H.count
  · exact (hkeep _ (by unfold slot; omega)).trans H.query
  · intro i hi
    exact (hkeep _ (by unfold ReportingHostFrontierLayout.left slot; omega)).trans (H.left i hi)
  · intro i hi
    exact (hkeep _ (by unfold ReportingHostFrontierLayout.right ReportingHostFrontierLayout.left slot; omega)).trans (H.right i hi)




























































































end ThreeSum.LightReportingWantedInitialize

end

section


/-!
# The wanted initializer with a retained counter before decoded rows

This is the same actual 42-procedure program. The dense counter and its
threshold precede the per-wanted decoded and packed rows, so the existing
decoder's prefix frame preserves the running state. The postcondition tracks
the exact counter update and preserves every other cell before packed rows.
-/

namespace ThreeSum.LightReportingWantedInitializeSeparated

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostLevelData ReportingHostFrontierLayout LightReportingWantedInitialize

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets_sourceProof {μ : ℕ→ℤ}
    {h J baseL baseR catalogs cover rawRows rows counter root maskBase work old threshold d : ℕ} {D : Catalog}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.zero_le J) pMod shift B C b c w.2.2)
    (HB : Bounds h J 0 D baseL baseR rows)
    (HW : Scratch lim h J 0 D B.card C.card maskBase work)
    (hmeta : SegN μ catalogs (D.record h 0)) (hmetaEnd : catalogs+5≤rows)
    (hgroup : μ (cover+3)=(groupSize h : ℤ)) (hcoverEnd : cover+4≤rows)
    (hraw : rawRows+J≤rows) (hrows : rows+J≤root) (hcounter : counter+2≤rawRows)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) 1≤maskBase)
    (hpackSpace : work+(512*h+1)≤lim.space)
    (hword : ((old+rootMass (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hreadRaw : SegN μ rawRows (rawMasks (outputRows w.2.2)))
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hd : d+2*width h J+16≤lim.depth) :
    Meets lim program 41 d
      [width h J,sourceCut h J,J,512*h,baseL,baseR,catalogs,rawRows,rows,cover,counter,root,maskBase,work]
      μ (time h J D.t)
      (fun result ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        result=(if threshold<old+rootMass I w then 1 else 0 : ℤ) ∧
        ν counter=((old+rootMass I w : ℕ) : ℤ) ∧
        At ν I w root (capacity I w) 0 ∧
        ν (root+2)=(rootMass I w : ℤ) ∧ ν (root+3)=(capacity I w : ℤ) ∧
        SegN ν rows (packedMasks (outputRows w.2.2)) ∧ KeptBut μ ν rows counter 1) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  have hwork := HW.masks
  have hspace := HW.space
  have hout' : root+4+2*capacity I w≤maskBase := by simpa [slot,Nat.add_assoc] using hout
  have hpackWord : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.le_mul_of_pos_left _ (by omega))).trans HW.word
  have hthresholdZ : μ (((counter : ℤ)+1).toNat)=(threshold : ℤ) := by
    rw [show ((counter : ℤ)+1).toNat=counter+1 by omega]
    exact hthreshold
  apply Meets.of_body (p := 41) (by rfl : program[41]?=some (body 0 39 40))
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
    (refine Light.Ends.setToThen (threshold : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hthreshold, hthresholdZ, LightBlockMasks.time,
                LightReportingInitializeStored.time, LightDenseGuard.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hthreshold, hthresholdZ, LightBlockMasks.time,
                LightReportingInitializeStored.time, LightDenseGuard.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hthreshold, hthresholdZ,
                LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hpack := (LightBlockMasks.program_meets (μ := μ) (d := d+1) (src := rawRows) (dst := rows) (work := work)
    (outputRows w.2.2) hw (by omega) (by omega) (Or.inl hraw) hpackSpace hpackWord hreadRaw (by omega)).append
      (LightReportingInitializeStored.program.map (ReportingHostRelocation.relocate 2) ++
        LightDenseGuard.program.map (ReportingHostRelocation.relocate 40) ++ [body 0 39 40])
  change Meets lim program 0 (d+1) _ μ (LightBlockMasks.time J (512*h)) _ at hpack
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
      | refine Light.Ends.callToThen (hpack _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hpack ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightBlockMasks.time,
                LightReportingInitializeStored.time, LightDenseGuard.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro qmask ν₁ ⟨hQ, hpacked, hkeepPack⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkeepPackRows : Kept μ ν₁ rows := by
    intro i hi
    exact hkeepPack i ⟨by omega,Or.inl hi⟩
  have HS₁ := HS.of_kept HB hkeepPackRows
  have HC₁ := HC.of_kept HB hkeepPackRows
  have hmeta₁ : SegN ν₁ catalogs (D.record h 0) := by
    intro i hi
    have hi' : i<5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
    exact (hkeepPackRows _ (by omega)).trans (hmeta i hi)
  have hgroup₁ : ν₁ (cover+3)=(groupSize h : ℤ) :=
    (hkeepPackRows _ (by omega)).trans hgroup
  have hinit := LightReportingInitializeStored.program_meets (μ := ν₁) (depth := d+1)
    pMod shift A B C a b c w hkey hw HS₁ HC₁ (HB.mono (by omega)) HW
    hmeta₁ (by omega) hgroup₁ (by omega) hout (by omega)
  have hinitRun := (ReportingHostRelocation.meets hinit LightBlockMasks.program).append
    (LightDenseGuard.program.map (ReportingHostRelocation.relocate 40) ++ [body 0 39 40])
  change Meets lim program 39 (d+1) _ ν₁ (LightReportingInitializeStored.time h J D.t) _ at hinitRun
  have hQzero : subsetMask (querySet 0 (outputRows w.2.2))=
      subsetMask (indexSet (flat (outputRows w.2.2))) := by rw [query_zero]
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
      | refine Light.Ends.callToThen (hinitRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hinitRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hQ,
                hQzero, LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hQ, hQzero, LightBlockMasks.time,
                LightReportingInitializeStored.time, LightDenseGuard.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hQ, hQzero,
                LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro unused ν₂ ⟨_, hfrontier, hmass, hcap, hkeepInit⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  change At ν₂ I w root (capacity I w) 0 at hfrontier
  change ν₂ (root+2)=(rootMass I w : ℤ) at hmass
  change ν₂ (root+3)=(capacity I w : ℤ) at hcap
  have hcounter₂ : ν₂ counter=(old : ℤ) := by
    refine (hkeepInit _ (by omega)).trans ?_
    exact (hkeepPackRows _ (by omega)).trans hcounterRead
  have hguard := LightDenseGuard.program_meets (μ := ν₂) (d := d+1)
    hw (by omega) (by omega) hword hcounter₂ hmass
  have hguardRun := (ReportingHostRelocation.meets hguard initialLibraries).append [body 0 39 40]
  change Meets lim program 40 (d+1) _ ν₂ LightDenseGuard.time _ at hguardRun
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
      | refine Light.Ends.callToThen (hguardRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hguardRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightBlockMasks.time, LightReportingInitializeStored.time,
                LightDenseGuard.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, LightBlockMasks.time,
                LightReportingInitializeStored.time, LightDenseGuard.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result ν₃ ⟨hresult, hcounter₃, hkeepGuard⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hkeepAbove : ∀ i, root ≤ i → ν₃ i=ν₂ i := fun i hi => hkeepGuard i (Or.inr (by omega))
  refine ⟨hresult,hcounter₃,frontier_of_above hfrontier hkeepAbove,
    (hkeepAbove _ (by omega)).trans hmass,(hkeepAbove _ (by omega)).trans hcap,?_,?_⟩
  · intro i hi
    have hi' : i<J := by simpa only [List.length_map,packedMasks_length] using hi
    exact (hkeepGuard _ (Or.inr (by omega))).trans ((hkeepInit _ (by omega)).trans (hpacked i hi))
  · intro i hi
    exact (hkeepGuard _ hi.2).trans
      ((hkeepInit _ (by omega)).trans (hkeepPackRows i hi.1))


end ThreeSum.LightReportingWantedInitializeSeparated

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J baseL baseR catalogs cover rawRows rows counter root maskBase work old threshold d : Nat}
  {D : ThreeSum.ReportingHostLevelData.Catalog} (pMod shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β)
  (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int) (w : ThreeSum.RawReporting.Wanted.{u_1} h J α),
  And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
        (@Prod.fst.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                (a
                  (@Prod.fst.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))
                pMod)
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (ThreeSum.RawIncidences.lift
                  (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput h J)
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w)))
                pMod))
            shift)
          (@ThreeSum.GlobalEncoding.globalKey h J
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w))))) →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @ThreeSum.ReportingHostLevelData.Sources.{u_2, u_3} β γ h J μ pMod shift B C b c
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{u_1, 0} α
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))
          baseL baseR →
        @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) μ D (Nat.zero_le J) pMod shift B C b c
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w)) →
          ThreeSum.ReportingHostLevelData.Bounds h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D
              baseL baseR rows →
            ThreeSum.ReportingHostLevelData.Scratch lim h J
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D (@Finset.card.{u_2} β B)
                (@Finset.card.{u_3} γ C) maskBase work →
              Light.SegN μ catalogs (D.record h (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) catalogs
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    rows →
                  @Eq.{1} Int
                      (μ
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.groupSize h)) →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        rows →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRows J) rows →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rows J) root →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              rawRows →
                            @LE.le.{0} Nat instLENat
                                (ThreeSum.ReportingHostFrontierLayout.slot root
                                  (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
                                    (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                                      (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                                        (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                        (Finset.{max (max u_2 u_3) u_1}
                                          (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                                        (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                                        (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                                          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                          (@Finset.instSProd.{u_2, u_3} β γ) B C))
                                      a b c)
                                    w)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                maskBase →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  lim.space →
                                @LE.le.{0} Int Int.instLEInt
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                                            (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst h
                                              J
                                              (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                                                (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                                                  (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                                  (Finset.{max (max u_2 u_3) u_1}
                                                    (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                                                  (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                                                  (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β)
                                                    (Finset.{u_3} γ) (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                                    (@Finset.instSProd.{u_2, u_3} β γ) B C))
                                                a b c)
                                              w))
                                          threshold)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    lim.word →
                                  Light.SegN μ rawRows
                                      (@ThreeSum.BlockMaskLayout.rawMasks J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        (@ThreeSum.BlockForced.outputRows h J
                                          (@Prod.snd.{0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                            (@Prod.snd.{u_1, 0} α
                                              (Prod.{0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                              w)))) →
                                    @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old) →
                                      @Eq.{1} Int
                                          (μ
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@Nat.cast.{0} Int instNatCastInt threshold) →
                                        @LE.le.{0} Nat instLENat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (ThreeSum.LightBlockQuery.width h J)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                                            lim.depth →
                                          Light.Meets lim ThreeSum.LightReportingWantedInitialize.program
                                            (@OfNat.ofNat.{0} Nat (nat_lit 41) (instOfNatNat (nat_lit 41))) d
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.LightBlockQuery.sourceCut h J))
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                                  (@List.cons.{0} Int
                                                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                                      (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                                      (@Nat.cast.{0} Int instNatCastInt h))
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt catalogs)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawRows)
                                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt cover)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt counter)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt root)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt work)
                                                                        (@List.nil.{0} Int)))))))))))))))
                                            μ (ThreeSum.LightReportingWantedInitialize.time h J D.t)
                                            fun (result : Int) (ν : Nat → Int) =>
                                            have I :=
                                              @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                                                (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                                                  (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                                  (Finset.{max (max u_2 u_3) u_1}
                                                    (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                                                  (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                                                  (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β)
                                                    (Finset.{u_3} γ) (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                                                    (@Finset.instSProd.{u_2, u_3} β γ) B C))
                                                a b c;
                                            And
                                              (@Eq.{1} Int result
                                                (@ite.{1} Int
                                                  (@LT.lt.{0} Nat instLTNat threshold
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                                                      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α
                                                        β γ inst h J I w)))
                                                  (threshold.decLt
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                                                      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α
                                                        β γ inst h J I w)))
                                                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
                                              (And
                                                (@Eq.{1} Int (ν counter)
                                                  (@Nat.cast.{0} Int instNatCastInt
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                                                      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α
                                                        β γ inst h J I w))))
                                                (And
                                                  (@ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h
                                                    J ν I w root
                                                    (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β
                                                      γ inst h J I w)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (And
                                                    (@Eq.{1} Int
                                                      (ν
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          root
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                            (instOfNatNat (nat_lit 2)))))
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3}
                                                          α β γ inst h J I w)))
                                                    (And
                                                      (@Eq.{1} Int
                                                        (ν
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) root
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2,
                                                                u_3}
                                                            α β γ inst h J I w)))
                                                      (And
                                                        (Light.SegN ν rows
                                                          (@ThreeSum.BlockMaskLayout.packedMasks J
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                (instOfNatNat (nat_lit 512)))
                                                              h)
                                                            (@ThreeSum.BlockForced.outputRows h J
                                                              (@Prod.snd.{0, 0}
                                                                (Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3))))
                                                                (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                                                (@Prod.snd.{u_1, 0} α
                                                                  (Prod.{0, 0}
                                                                    (Fin
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                        (instOfNatNat (nat_lit 3))))
                                                                    (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                                                  w)))))
                                                        (Light.KeptBut μ ν rows counter
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))))) := by
  exact @ThreeSum.LightReportingWantedInitializeSeparated.program_meets_sourceProof

#print axioms solution
