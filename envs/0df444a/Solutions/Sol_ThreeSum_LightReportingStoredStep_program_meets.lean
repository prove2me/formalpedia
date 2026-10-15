-- Prove2me | solution 1 for ThreeSum.LightReportingStoredStep.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:48:01.938994+00:00
-- url     : https://prove2.me/submissions/cc732487-dfa6-4ea4-8987-e20a404f9645

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childPrefixes_length
import Theorems.Thm_ThreeSum_LightReportingFrontierStep_program_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum_ReportingHostMasks_querySet_step
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass
import Theorems.Thm_ThreeSum_StoredReporting_positivePrefix_valid


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
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
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
namespace ThreeSumApsp
end ThreeSumApsp

section


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators











@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

















































































@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ prefixIndices J k ↔ i.val < k := by simp [prefixIndices]



















end ThreeSum.BlockRows

end

section


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false




@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]







@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (Coord J L)) (c : Coord J L) :
    coordEquiv J L c ∈ indexSet S ↔ c ∈ S := by
  simp [indexSet]





































































































end ThreeSum.BlockIndex

end

section


/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery

open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false







theorem suffixStage_le (J L k : ℕ) : suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)






















































































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]






































































end Histograms

end ThreeSum.BlockIndexedQuery

end

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]







































theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by
  have h := subsetMask_union_sdiff Q U hU
  have hz : (subsetMask U : ℤ)+(subsetMask (Q \ U) : ℤ) = (subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

end

section


/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators







theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    subsetMask (indexSet (join I rows)) = ∑ i ∈ I, rowMask rows i := by
  rw [MaskDifference.subsetMask_sum]
  unfold indexSet
  rw [Finset.sum_map]
  unfold join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,coordEquiv_val,pow_add,rowMask,
    MaskDifference.subsetMask_sum,Finset.mul_sum]

theorem prefixMask_eq_sum {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    prefixMask rows k = ∑ i ∈ prefixIndices J k, rowMask rows i := mask_join _ _






theorem prefixIndices_succ {J k : ℕ} (hk : k < J) :
    prefixIndices J (k+1) = insert ⟨k,hk⟩ (prefixIndices J k) := by
  ext i
  simp only [mem_prefixIndices,Finset.mem_insert,Fin.ext_iff]
  omega

theorem prefixMask_succ {J L k : ℕ} (rows : Fin J → Finset (Fin L)) (hk : k < J) :
    prefixMask rows (k+1) = prefixMask rows k+rowMask rows ⟨k,hk⟩ := by
  rw [prefixMask_eq_sum,prefixIndices_succ hk,Finset.sum_insert (by simp),prefixMask_eq_sum]
  exact Nat.add_comm _ _









theorem prefixMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    prefixMask rows k < 2^(J*L) := (subsetMask_isMask _).1

theorem rowMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) :
    rowMask rows i < 2^(J*L) := by
  have he : prefixMask rows (i.val+1) = prefixMask rows i.val+rowMask rows i :=
    prefixMask_succ rows i.isLt
  have hb := prefixMask_lt rows (i.val+1)
  omega

















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
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
































































































































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]































































end Light

end
end

section


/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates

open Finset ThreeSum.SubsetAddress
open scoped BigOperators











































































theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he





















































































































theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).Nodup := by
  unfold missingSets
  apply (setLayer_nodup _ (List.nodup_reverse.mpr (positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp ha
  have hbs := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,positions_toFinset] at has hbs
  have h := congrArg natPositions he
  rw [decode_maskOf (has.1.trans (natPositions_subset Q)),
      decode_maskOf (hbs.1.trans (natPositions_subset Q))] at h
  exact h




























end ThreeSum.QueryCoordinates

end

section


/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix

variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]








theorem residual_le_suffix {h J k : ℕ} : residualSize h J k ≤ suffixStage J (512*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)






























































end ThreeSum.LightReportingSuffixBoxes

end

section


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced




@[simp] theorem mem_blockSet {J L : ℕ} (i j : Fin J) (S : Finset (Fin L)) (x : Fin L) :
    coordEquiv J L ⟨j,x⟩ ∈ blockSet i S ↔ j = i ∧ x ∈ S := by
  simp [blockSet]





@[simp] theorem blockSet_mask {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    subsetMask (blockSet i S) = 2^(i.val*L)*subsetMask S := by
  simp [blockSet,mask_join,rowMask]












































theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _



















theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]



























































































theorem blockSet_subset_query {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) ⊆ querySet k Q := by
  intro x hx
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  obtain ⟨rfl,ha⟩ := (mem_blockSet _ _ _ _).mp hx
  simp only [querySet,mem_indexSet,remaining,mem_join,Finset.mem_compl,mem_prefixIndices]
  exact ⟨by simp,ha⟩

theorem queryMask_step {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    (subsetMask (querySet k Q) : ℤ)-(rowMask Q ⟨k,hk⟩ : ℤ) =
      (subsetMask (querySet (k+1) Q) : ℤ) := by
  rw [querySet_step Q hk]
  have he : rowMask Q ⟨k,hk⟩ = subsetMask (blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩)) := by
    simp [rowMask]
  rw [he]
  exact MaskDifference.subsetMask_sdiff_int _ _ (blockSet_subset_query Q hk)
















































end ThreeSum.ReportingHostMasks

end

section


/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier

open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators




theorem mem_children_iff {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (512*h))) : S ∈ children q k ↔ S ∈ RawReporting.children q k := by
  unfold children RawReporting.children
  split
  · exact localChildren_mem _ _ _ _
  · rfl

theorem children_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact localChildren_nodup _ _ _
  · exact List.nodup_nil









section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem word_children {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word,partitionWord_length]; exact hj) ∈ children w.2.2 j :=
  (mem_children_iff _ _ _).mpr (RawReporting.word_children I w r hr j hj)





















theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) : (frontier I w k).length ≤ (domain I w).card := by
  have h := Reporting.frontier_length_le_mass (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) (children_nodup w.2.2) hk
  simpa only [frontier,Finset.sum_const,smul_eq_mul,mul_one] using h
























































end Indices

end ThreeSum.ReportingHostFrontier

end

section


/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive

open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators

set_option linter.unusedSectionVars false

theorem map_range_getD {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi',Option.getD_some]

theorem selected_map {α : Type*} (xs : List α) (fallback : α) (q : α → ℕ) :
    (LightReportingFilter.selected (fun i => q (xs[i]?.getD fallback)) xs.length).map
        (fun i => xs[i]?.getD fallback) = xs.filter (fun x => 0 < q x) := by
  change ((List.range xs.length).filter
    ((fun x : α => decide (0 < q x)) ∘ (fun i => xs[i]?.getD fallback))).map
      (fun i => xs[i]?.getD fallback) = _
  rw [← List.filter_map,map_range_getD]

theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







theorem positiveChildren_eq_filter {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    positiveChildren I w pre hk =
      (childPrefixes w.2.2 pre hk).filter (fun next => 0 < prefixQuery I w (k+1) next) := by
  unfold positiveChildren
  change (LightReportingFilter.selected
    (fun i => prefixQuery I w (k+1) ((childPrefixes w.2.2 pre hk)[i]?.getD [])) (groupSize h)).map
      (fun i => (childPrefixes w.2.2 pre hk)[i]?.getD []) = _
  rw [← childPrefixes_length w.2.2 pre hk]
  exact selected_map (childPrefixes w.2.2 pre hk) [] (prefixQuery I w (k+1))







theorem frontier_valid {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (512*h)))}
    (hp : pre ∈ ReportingHostFrontier.frontier I w k) : ValidPrefix w.2.2 k pre :=
  positivePrefix_valid I w pre hk (frontier_positive _ _ hp)

theorem frontier_step {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k < J) :
    ReportingHostFrontier.frontier I w (k+1) =
      (ReportingHostFrontier.frontier I w k).flatMap (fun pre => positiveChildren I w pre hk) := by
  simp only [ReportingHostFrontier.frontier,Reporting.frontier,List.filter_flatMap,
    positiveChildren_eq_filter,ReportingHostFrontier.children,dif_pos hk,childPrefixes]














end ThreeSum.ReportingHostPositive

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





@[simp] theorem slot_zero (base cap : ℕ) : slot base cap 0=base := by simp [slot]
theorem slot_succ (base cap k : ℕ) : slot base cap (k+1)=slot base cap k+4+2*cap := by
  unfold slot; ring

theorem slot_mono {base cap i j : ℕ} (hij : i≤j) : slot base cap i≤slot base cap j := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _






















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem rootMass_eq {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w=(domain I w).card := by
  simp [rootMass,prefixQuery,Reporting.mass,Subset.fiberMass]




theorem group_pos (h : ℕ) : 0<groupSize h := Nat.choose_pos (by omega)

theorem capacity_pos {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    0<capacity I w := Nat.mul_pos (by omega) (group_pos h)

theorem mass_lt_capacity {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w<capacity I w :=
  (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_right _ (group_pos h))

theorem frontier_capacity {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (hk : k≤J) : (ReportingHostFrontier.frontier I w k).length≤capacity I w := by
  have hh := ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← rootMass_eq I w] at hh
  exact hh.trans (mass_lt_capacity I w).le

theorem expansion_capacity {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (hk : k≤J) : (ReportingHostFrontier.frontier I w k).length*groupSize h≤capacity I w := by
  have hh := ReportingHostFrontier.frontier_length_le_domain I w hk
  rw [← rootMass_eq I w] at hh
  exact Nat.mul_le_mul_right (groupSize h) (hh.trans (Nat.le_succ _))




















































end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# One actual reporting level from persistent physical headers

The host reads the previously computed capacity and frontier count, the
packed next output row, and the shared five-cell catalog record. It invokes
the complete multi-parent expansion and writes the new physical header.
-/

namespace ThreeSum.LightReportingStoredStep

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout ReportingHostMasks

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false






























variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets_sourceProof {μ : ℕ→ℤ}
    {h J k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : ℕ}
    {D : Catalog} (hk : k<J)
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.succ_le_of_lt hk) pMod shift B C b c w.2.2)
    (HB : Bounds h J (k+1) D baseL baseR root)
    (HW : Scratch lim h J (k+1) D B.card C.card maskBase work)
    (hmeta : SegN μ (catalogs+5*(k+1)) (D.record h (k+1)))
    (hmetaEnd : catalogs+5*(k+1)+5≤root)
    (hrows : rows+J≤root)
    (hrow : μ (rows+k)=(rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ))
    (hcap : μ (root+3)=(capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : At μ (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) k)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) (k+2)≤masks)
    (hmasks : masks+groupSize h≤childL) (hchildL : childL+groupSize h≤childR)
    (hchildR : childR+groupSize h≤counts) (hcounts : counts+groupSize h≤selected)
    (hselected : selected+groupSize h≤maskBase)
    (hparams : J+512*h+groupSize h+sourceCut h J≤lim.space)
    (hd : depth+2*width h J+18≤lim.depth) :
    Meets lim program 51 depth
      [width h J,h,J,k+1,baseL,baseR,catalogs,rows,root,masks,childL,childR,counts,selected,maskBase,work,
        groupSize h,sourceCut h J,512*h]
      μ (time h J k D.t (ReportingHostFrontier.frontier (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k).length)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
        At ν I w root (capacity I w) (k+1) ∧ Kept μ ν (slot root (capacity I w) (k+1))) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := capacity I w
  let pres := ReportingHostFrontier.frontier I w k
  let old := slot root cap k
  let dest := slot root cap (k+1)
  let catalogRow := catalogs+5*(k+1)
  let prefixCardNext := (k+1)*h
  let offsetNext := (k+1)*(512*h)
  let stageNext := suffixStage J (512*h) (k+1)
  let residualNext := residualSize h J (k+1)
  change At μ I w root cap k at HA
  change μ (root+3)=(cap : ℤ) at hcap
  change slot root cap (k+2)≤masks at hout
  change Meets lim program 51 depth _ μ (time h J k D.t pres.length)
    (fun r ν => r=((ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
      At ν I w root cap (k+1) ∧ Kept μ ν dest)
  have hcapPos : 0<cap := capacity_pos I w
  have hprevCount : pres.length≤cap := frontier_capacity I w hk.le
  have hnextCount : (ReportingHostFrontier.frontier I w (k+1)).length≤cap := frontier_capacity I w (by omega)
  have hchildren : pres.length*groupSize h≤cap := expansion_capacity I w hk.le
  have hrootOld : root≤old := by simpa only [slot_zero] using (slot_mono (base := root) (cap := cap) (Nat.zero_le k))
  have hold : old+4+2*cap=dest := (slot_succ root cap k).symm
  have hdest : dest+4+2*cap≤masks := by
    have hh := slot_succ root cap (k+1)
    change slot root cap (k+2)=dest+4+2*cap at hh
    rwa [hh] at hout
  have hwork := HW.masks
  have hspace := HW.space
  have hpow := HW.powers
  have hmetaT := hmeta.getElem (i := 0) (by simp [Catalog.record])
  have hmetaCut := hmeta.getElem (i := 1) (by simp [Catalog.record])
  have hmetaIndex := hmeta.getElem (i := 2) (by simp [Catalog.record])
  have hmetaPtr := hmeta.getElem (i := 3) (by simp [Catalog.record])
  have hmetaN := hmeta.getElem (i := 4) (by simp [Catalog.record])
  simp only [Catalog.record,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at hmetaT hmetaCut hmetaIndex hmetaPtr hmetaN
  change μ catalogRow=(D.t : ℤ) at hmetaT
  change μ (catalogRow+1)=(D.boxCut : ℤ) at hmetaCut
  change μ (catalogRow+2)=(D.indexBase : ℤ) at hmetaIndex
  change μ (catalogRow+3)=(D.ptrBase : ℤ) at hmetaPtr
  change μ (catalogRow+4)=(count h (k+1) : ℤ) at hmetaN
  have hmetaBound : catalogRow+5≤root := hmetaEnd
  have hmetaIndexZ : μ (((catalogRow : ℤ)+2).toNat)=(D.indexBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+2).toNat=catalogRow+2 by omega]
    exact hmetaIndex
  have hmetaPtrZ : μ (((catalogRow : ℤ)+3).toNat)=(D.ptrBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+3).toNat=catalogRow+3 by omega]
    exact hmetaPtr
  have hmetaNZ : μ (((catalogRow : ℤ)+4).toNat)=(count h (k+1) : ℤ) := by
    rw [show ((catalogRow : ℤ)+4).toNat=catalogRow+4 by omega]
    exact hmetaN
  have hDindex := HB.index
  have hDptr := HB.pointers
  have ht := HW.t
  have hcut := HW.cut
  have hwidthSpace : width h J≤lim.space := by omega
  have hresLe : residualSize h J (k+1)≤width h J := by
    exact (LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k+1)).trans
      (suffixStage_le J (512*h) (k+1))
  change residualNext≤width h J at hresLe
  change D.t≤residualNext+1 at ht
  change D.boxCut≤residualNext at hcut
  have hstageLe := suffixStage_le J (512*h) (k+1)
  change stageNext≤width h J at hstageLe
  have hprefixCard : (k+1)*h≤width h J := by
    have hh := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hk)
    unfold width
    nlinarith
  have hoffset : (k+1)*(512*h)≤width h J := Nat.mul_le_mul_right _ (by omega)
  change prefixCardNext≤width h J at hprefixCard
  change offsetNext≤width h J at hoffset
  have hmask (S : Finset (Fin (width h J))) : (subsetMask S : ℤ)≤lim.word := by
    have hp : 2^(width h J)≤(width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask S).1.le.trans hp)).trans HW.word
  have hrowWord : (rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ)≤lim.word := by
    have hh := BlockMaskLayout.rowMask_lt (outputRows w.2.2) ⟨k,hk⟩
    have hb := hmask (blockSet ⟨k,hk⟩ (outputRows w.2.2 ⟨k,hk⟩))
    simpa [rowMask] using hb
  have hQ := hmask (querySet k (outputRows w.2.2))
  have hQnext := hmask (querySet (k+1) (outputRows w.2.2))
  have hreadQ : μ (old+1)=(subsetMask (querySet k (outputRows w.2.2)) : ℤ) := HA.query
  have hreadN : μ old=(pres.length : ℤ) := HA.count
  have hcapZ : μ (((root : ℤ)+3).toNat)=(cap : ℤ) := by
    rw [show ((root : ℤ)+3).toNat=root+3 by omega]
    exact hcap
  have hrowZ : μ (((rows : ℤ)+((k : ℤ)+1)).toNat-1)=
      (rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ) := by
    rw [show ((rows : ℤ)+((k : ℤ)+1)).toNat-1=rows+k by omega]
    exact hrow
  have readAdd (x y : ℕ) : μ (((x : ℤ)+(y : ℤ)).toNat)=μ (x+y) := by
    congr 1 <;> omega
  have hOldCalc : (root : ℤ)+(k : ℤ)*(4+2*(cap : ℤ))=(old : ℤ) := by
    simp only [old,slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hDestCalc : (root : ℤ)+((k : ℤ)+1)*(4+2*(cap : ℤ))=(dest : ℤ) := by
    simp only [dest,slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hMetaCalc : (catalogs : ℤ)+5*((k : ℤ)+1)=(catalogRow : ℤ) := by
    simp only [catalogRow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hSubtract : ((J-(k+1) : ℕ) : ℤ)=(J : ℤ)-((k : ℤ)+1) := by omega
  have hStageCalc : ((J : ℤ)-((k : ℤ)+1))*(512*(h : ℤ))=(stageNext : ℤ) := by
    simp only [stageNext,suffixStage,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hResidualCalc : ((J : ℤ)-((k : ℤ)+1))*(2*(h : ℤ))=(residualNext : ℤ) := by
    simp only [residualNext,residualSize,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hPrefixCalc : ((k : ℤ)+1)*(h : ℤ)=(prefixCardNext : ℤ) := by
    simp only [prefixCardNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hOffsetCalc : ((k : ℤ)+1)*(512*(h : ℤ))=(offsetNext : ℤ) := by
    simp only [offsetNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  apply Meets.of_body (p := 51) (by rfl : program[51]?=some (body 50))
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
    (refine Light.Ends.setToThen (cap : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcapZ,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcapZ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcapZ,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (4 + 2 * cap : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (old : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hOldCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hOldCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hOldCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (dest : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hDestCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hDestCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hDestCalc,
                LightReportingFrontierStep.time] <;>
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
        Light.Ends.setToThen (rowMask (outputRows w.2.2) ⟨k, hk⟩ : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrowZ,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hrowZ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hrowZ,
                LightReportingFrontierStep.time] <;>
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
        Light.Ends.setToThen (subsetMask (querySet k (outputRows w.2.2)) : ℕ) ?_
          ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readAdd,
                hreadQ, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readAdd, hreadQ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readAdd, hreadQ,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (catalogRow : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (D.t : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, readAdd, hmetaT, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, readAdd, hmetaT, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc, readAdd, hmetaT,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (D.boxCut : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, readAdd, hmetaCut, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, readAdd, hmetaCut,
                LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc, readAdd,
                hmetaCut, LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (D.indexBase : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, hmetaIndexZ, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, hmetaIndexZ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc, hmetaIndexZ,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (D.ptrBase : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, hmetaPtrZ, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, hmetaPtrZ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc, hmetaPtrZ,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (count h (k + 1) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hMetaCalc, hmetaNZ, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hMetaCalc, hmetaNZ, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hMetaCalc, hmetaNZ,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (stageNext : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hStageCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hStageCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hStageCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (prefixCardNext : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hPrefixCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hPrefixCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hPrefixCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (residualNext : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hResidualCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hResidualCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hResidualCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (offsetNext : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hOffsetCalc, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hOffsetCalc, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hOffsetCalc,
                LightReportingFrontierStep.time] <;>
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
    (refine Light.Ends.setToThen (pres.length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hreadN,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadN, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadN,
                LightReportingFrontierStep.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hrun := (LightReportingFrontierStep.program_meets (depth := depth+1) (μ := μ)
    (inL := old+4) (inR := old+4+cap) (outL := dest+4) (outR := dest+4+cap)
    pMod shift A B C a b c w pres hk
    (fun _ hp => ReportingHostPositive.frontier_valid I w hk.le hp) hkey hw
    (HB.left.trans (by omega)) (HB.right.trans (by omega))
    (HB.index.trans (by omega)) (HB.pointers.trans (by omega)) (HB.boxes.trans (by omega))
    (by omega) (by omega) (by omega) (by omega) hmasks hchildL hchildR hcounts hselected
    HW.masks HW.space HW.powers HW.emod HW.word HW.lookup HW.values HW.t HW.cut HW.flags
    HS.left HS.right HC.index HC.pointers HC.boxes HA.left HA.right (by omega)).append [body 50]
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
      | refine Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hrun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hSubtract, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hSubtract, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hSubtract,
                LightReportingFrontierStep.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result ν ⟨hresult, hnewL, hnewR, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hstep := ReportingHostPositive.frontier_step I w hk
  change result=((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).length : ℤ) at hresult
  change LightReportingPositiveExpand.KeptOutputs μ ν masks (dest+4) (dest+4+cap)
    (pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).length at hkept
  change SegN ν (dest+4) ((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) at hnewL
  change SegN ν (dest+4+cap) ((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) at hnewR
  have hpstep : pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)=
    ReportingHostFrontier.frontier I w (k+1) := hstep.symm
  rw [hpstep] at hresult hkept hnewL hnewR
  have hnextWord : ((ReportingHostFrontier.frontier I w (k+1)).length : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hnextCount.trans (by omega))).trans hw
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
        Light.Ends.setToThen
          (subsetMask (querySet (k + 1) (outputRows w.2.2)) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                queryMask_step, LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [queryMask_step, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, queryMask_step,
                LightReportingFrontierStep.time] <;>
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
        Light.Ends.storeToThen dest
          ((ReportingHostFrontier.frontier I w (k + 1)).length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hresult,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hresult, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hresult,
                LightReportingFrontierStep.time] <;>
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
        Light.Ends.storeToThen (dest + 1)
          (subsetMask (querySet (k + 1) (outputRows w.2.2)) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingFrontierStep.time] <;>
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
        Light.Ends.setToThen
          ((ReportingHostFrontier.frontier I w (k + 1)).length : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hresult,
                LightReportingFrontierStep.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hresult, LightReportingFrontierStep.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hresult,
                LightReportingFrontierStep.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨by simp,?_,?_⟩
  · constructor
    · change Function.update (Function.update ν dest _) (dest+1) _ dest=_
      simp
    · change Function.update (Function.update ν dest _) (dest+1) _ (dest+1)=_
      simp
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewL i hi
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+cap+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewR i hi
  · intro i hi
    change Function.update (Function.update ν dest _) (dest+1) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkept i ⟨by omega,Or.inl (by omega),Or.inl (by omega)⟩

end ThreeSum.LightReportingStoredStep

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : Nat}
  {D : ThreeSum.ReportingHostLevelData.Catalog} (hk : @LT.lt.{0} Nat instLTNat k J) (pMod shift : Int)
  (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (hkey :
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
                w))))))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (HS :
    @ThreeSum.ReportingHostLevelData.Sources.{u_2, u_3} β γ h J μ pMod shift B C b c
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      baseL baseR)
  (HC :
    @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J k.succ μ D (@Nat.succ_le_of_lt k J hk) pMod shift B C b c
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w)))
  (HB :
    ThreeSum.ReportingHostLevelData.Bounds h J
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      D baseL baseR root)
  (HW :
    ThreeSum.ReportingHostLevelData.Scratch lim h J
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      D (@Finset.card.{u_2} β B) (@Finset.card.{u_3} γ C) maskBase work)
  (hmeta :
    Light.SegN μ
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) catalogs
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (D.record h
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hmetaEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) catalogs
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      root)
  (hrows : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rows J) root)
  (hrow :
    @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rows k))
      (@Nat.cast.{0} Int instNatCastInt
        (@ThreeSum.BlockMaskLayout.rowMask J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
          (@ThreeSum.BlockForced.outputRows h J
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J)
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                w)))
          (@Fin.mk J k hk))))
  (hcap :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) root
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Nat.cast.{0} Int instNatCastInt
        (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
          (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
            (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
              (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
              (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
              (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
            a b c)
          w)))
  (HA :
    @ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J μ
      (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
        a b c)
      w root
      (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
        (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
          (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
            (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
            (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
            (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
          a b c)
        w)
      k)
  (hout :
    @LE.le.{0} Nat instLENat
      (ThreeSum.ReportingHostFrontierLayout.slot root
        (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J
          (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
            (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
              (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
              (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
              (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
            a b c)
          w)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      masks)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks (ThreeSum.LocalCoverBounds.groupSize h))
      childL)
  (hchildL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) childL (ThreeSum.LocalCoverBounds.groupSize h))
      childR)
  (hchildR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) childR (ThreeSum.LocalCoverBounds.groupSize h))
      counts)
  (hcounts :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counts (ThreeSum.LocalCoverBounds.groupSize h))
      selected)
  (hselected :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) selected (ThreeSum.LocalCoverBounds.groupSize h))
      maskBase)
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (ThreeSum.LocalCoverBounds.groupSize h))
        (ThreeSum.LightBlockQuery.sourceCut h J))
      lim.space)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (ThreeSum.LightBlockQuery.width h J)))
        (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
      lim.depth),
  Light.Meets lim ThreeSum.LightReportingStoredStep.program
    (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51))) depth
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.width h J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
          (@List.cons.{0} Int
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt k)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseL)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt baseR)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt catalogs)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt root)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt childL)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt childR)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counts)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt selected)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                    (@List.cons.{0} Int
                                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.groupSize h))
                                      (@List.cons.{0} Int
                                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockQuery.sourceCut h J))
                                        (@List.cons.{0} Int
                                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                            (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                            (@Nat.cast.{0} Int instNatCastInt h))
                                          (@List.nil.{0} Int))))))))))))))))))))
    μ
    (ThreeSum.LightReportingStoredStep.time h J k D.t
      (@List.length.{0}
        (List.{0}
          (Finset.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
        (@ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J
          (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
            (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
              (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
              (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
              (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
              (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
            a b c)
          w k)))
    fun (r : Int) (ν : Nat → Int) =>
    have I :=
      @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
        a b c;
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@List.length.{0}
            (List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
            (@ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J I w
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
      (And
        (@ThreeSum.ReportingHostFrontierLayout.At.{u_1, u_2, u_3} α β γ inst h J ν I w root
          (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Light.Kept μ ν
          (ThreeSum.ReportingHostFrontierLayout.slot root
            (@ThreeSum.ReportingHostFrontierLayout.capacity.{u_1, u_2, u_3} α β γ inst h J I w)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  exact @ThreeSum.LightReportingStoredStep.program_meets_sourceProof

#print axioms solution
