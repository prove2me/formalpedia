-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixCatalog.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:20:08.785298+00:00
-- url     : https://prove2.me/submissions/6fd88b7c-fbe4-4e49-ab1f-cbebd45e63e1

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_ThreeSum_LightReportingPrefixArrays_program_meets
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalogSetup_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_length
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
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixMasks
end ThreeSum.ReportingHostPrefixMasks
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


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators










































































theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (join I u).card = I.card * h := by
  rw [join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]













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











@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (Coord J L)) :
    (indexSet S).card = S.card := Finset.card_map _


































































































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

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (prefixIndices J k).card = k := by
  simpa only [prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))

















































theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) : (leftPrefix k u).card = k*h := by
  rw [leftPrefix,indexSet_card,prefixLeft,join_card_of_balance _ _ hu,prefixIndices_card hk]







































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
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog

open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix

set_option linter.unusedSectionVars false



















theorem leftSet_card {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    (leftSet (J := J) p).card = k*h := by
  apply leftPrefix_card hk
  intro i hi
  simp only [leftRows,dif_pos (mem_prefixIndices.mp hi)]
  exact (edge_data _).1

theorem rightSet_card {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    (rightSet (J := J) p).card = k*h := by
  apply leftPrefix_card hk
  intro i hi
  simp only [rightRows,dif_pos (mem_prefixIndices.mp hi)]
  exact (edge_data _).2.1


































section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

















































end Sources

end ThreeSum.ReportingHostPrefixCatalog

end

section


/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks

open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}

theorem positionalHash_ofFn (p : ℤ) (raw : α → ℤ) {k : ℕ} (f : Fin k → α) :
    Radix.positionalHash p raw (List.ofFn f) = ∑ i : Fin k, p^i.val*raw (f i) := by
  induction k with
  | zero => simp [Radix.positionalHash]
  | succ k ih =>
    rw [List.ofFn_succ,Radix.positionalHash,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem mask_rows_ofFin {J L k : ℕ} (hk : k ≤ J) (u : Fin k → Finset (Fin L)) :
    subsetMask (leftPrefix k (fun i : Fin J => if hi : i.val < k then u ⟨i.val,hi⟩ else ∅)) =
      ∑ i : Fin k, 2^(i.val*L)*subsetMask (u i) := by
  rw [leftPrefix,prefixLeft,mask_join]
  refine Finset.sum_bij (fun i hi => (⟨i.val,mem_prefixIndices.mp hi⟩ : Fin k)) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · intro i hi
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,mem_prefixIndices.mpr i.isLt,rfl⟩
  · intro i hi
    simp only [rowMask,dif_pos (mem_prefixIndices.mp hi)]






theorem leftSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (leftSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.1 := by
  unfold leftSet leftRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.1)

theorem rightSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (rightSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.2 := by
  unfold rightSet rightRows
  exact mask_rows_ofFin (J := J) (L := 512*h) (k := k) hk (fun i => (p i).val.2)

theorem leftHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.1 : ℤ)) (tuple p) =
      (subsetMask (leftSet (J := J) p) : ℤ) := by
  rw [tuple,positionalHash_ofFn,leftSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]

theorem rightHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.2 : ℤ)) (tuple p) =
      (subsetMask (rightSet (J := J) p) : ℤ) := by
  rw [tuple,positionalHash_ofFn,rightSet_mask hk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← pow_mul,Nat.mul_comm]





















theorem tuple_ofTuple {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ pairs (512*h) h) :
    tuple (ofTuple xs hlen hmem) = xs := by
  apply List.ext_getElem
  · simp [tuple,hlen]
  · intro i hi hi'
    simp [tuple,ofTuple]


























end ThreeSum.ReportingHostPrefixMasks

end

section


/-!
# Complete shared prefix records in the physical product-constructor order

The semantic list is obtained from the actual tuple list, without filtering,
reordering, or coalescing equal left/right projections. It connects both
constructed integer arrays to every exact global prefix-mask pair.
-/

namespace ThreeSum.ReportingHostPrefixOrder

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments

set_option maxHeartbeats 600000







theorem prefixes_length (h k : ℕ) :
    (prefixes h k).length = ((512*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [prefixes,List.length_map,List.length_attach,RadixKeyLists.tuples_length,pairs_length]

theorem prefixes_tuple (h k : ℕ) :
    (prefixes h k).map tuple = RadixKeyLists.tuples (pairs (512*h) h) k := by
  unfold prefixes
  simp only [List.map_map,Function.comp_def,tuple_ofTuple]
  simp






















theorem left_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (leftMasks (512*h) h) k =
      (leftSets h J k).map (fun S => (subsetMask S : ℤ)) := by
  rw [leftMasks,RadixKeyLists.values_eq_map,← prefixes_tuple]
  simp only [List.map_map,leftSets,Function.comp_def,leftHash_eq_mask hk]

theorem right_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (rightMasks (512*h) h) k =
      (rightSets h J k).map (fun S => (subsetMask S : ℤ)) := by
  rw [rightMasks,RadixKeyLists.values_eq_map,← prefixes_tuple]
  simp only [List.map_map,rightSets,Function.comp_def,rightHash_eq_mask hk]

theorem preL_get {h J k i : ℕ} (hi : i < (prefixes h k).length) :
    preL h J k i = leftSet (J := J) (prefixes h k)[i] := by
  simp only [preL,leftSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preR_get {h J k i : ℕ} (hi : i < (prefixes h k).length) :
    preR h J k i = rightSet (J := J) (prefixes h k)[i] := by
  simp only [preR,rightSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preL_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preL h J k i).card = k*h := by rw [preL_get hi]; exact leftSet_card hk _

theorem preR_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preR h J k i).card = k*h := by rw [preR_get hi]; exact rightSet_card hk _
















end ThreeSum.ReportingHostPrefixOrder

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























theorem count_eq_length (h k : ℕ) : count h k = (prefixes h k).length :=
  (prefixes_length h k).symm

theorem count_pos (h k : ℕ) : 0 < count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem readL {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.leftMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preL h J k i) : ℤ) := by
  rw [ReportingHostPrefixOrder.left_values hk] at hs
  intro i hi
  have hi' : i < (prefixes h k).length := by rwa [← count_eq_length]
  have hh := hs i (by simpa only [leftSets,List.length_map] using hi')
  simpa only [leftSets,List.getElem_map,preL_get hi'] using hh

theorem readR {h J k a : ℕ} {μ : ℕ → ℤ} (hk : k ≤ J)
    (hs : Seg μ a (RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ)
      (ReportingHostPairSegments.rightMasks (512*h) h) k)) :
    ∀ i < count h k, μ (a+i) = (subsetMask (preR h J k i) : ℤ) := by
  rw [ReportingHostPrefixOrder.right_values hk] at hs
  intro i hi
  have hi' : i < (prefixes h k).length := by rwa [← count_eq_length]
  have hh := hs i (by simpa only [rightSets,List.length_map] using hi')
  simpa only [rightSets,List.getElem_map,preR_get hi'] using hh

theorem program_meets_sourceProof {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(512*h)) (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hS : srcS+(512*h).choose h ≤ pairL)
    (hL : pairL+LightReportingPrefixArrays.localCount (512*h) h ≤ pairR)
    (hR : pairR+LightReportingPrefixArrays.localCount (512*h) h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (LightReportingPrefixArrays.localCount (512*h) h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (LightReportingPrefixArrays.localCount (512*h) h) k ≤ ptrBase)
    (hptr : ptrBase+count h k ≤ boxBase)
    (hbox : boxBase+count h k*stride ((J-k)*(512*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap ((J-k)*(512*h)) boxCut ≤ work)
    (hpairSpace : work+2*(512*h)+2 ≤ lim.space)
    (hspace : work+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+5 ≤ lim.depth) (hd : d+J*(512*h)+14 ≤ lim.depth) :
    Meets lim program 43 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),baseL,baseR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work]
      μ (time h J k boxCut)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ) ∧
        SegN μ' ptrBase (List.ofFn fun i : Fin (count h k) =>
          boxBase+i.val*stride ((J-k)*(512*h)) boxCut) ∧
        (∀ i < count h k, LightBoxStages.StoredThrough μ'
          (boxBase+i*stride ((J-k)*(512*h)) boxCut) boxCut
          (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
          ((J-k)*(512*h))) ∧
        LightZetaStages.StoredThrough μ' baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough μ' baseR cut g (J*(512*h)) ∧
        μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k) =
          (count h k : ℤ) ∧
        (∀ i < count h k,
          μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preL h J k i) : ℤ)) ∧
        (∀ i < count h k,
          μ' (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preR h J k i) : ℤ)) ∧
        Kept μ μ' srcS) := by
  have hn := count_pos h k
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hptrOrder : stageR ≤ ptrBase := by unfold LightRadixKeys.space at hstageR; omega
  have hprefixEndL : stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageL.trans hptrOrder
  have hprefixEndR : stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+
      count h k ≤ ptrBase := hstageR
  have hkhWord : ((k*h : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : k*h ≤ lim.space)).trans hw
  have hkhWordZ : (k : ℤ)*(h : ℤ) ≤ lim.word := by simpa only [Nat.cast_mul] using hkhWord
  have hwidth : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  apply Meets.of_body (p := 43) (by rfl : program[43]? = some (body 10 42))
  unfold body time
  have hp := ((LightReportingPrefixArrays.program_meets (d := d+1) (μ := μ)
    hw (by omega) hS hL hR hstageL (hstageR.trans (by omega)) hpairSpace hpowWord hkeysWord (by omega)).append
      (LightReportingSuffixCatalogSetup.program.map
        (ReportingHostRelocation.relocate LightReportingPrefixArrays.program.length))).append [body 10 42]
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
      | refine Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hp ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro leftHead μ₁
              ⟨hhead, hcountL, hcountR, hleftArray, hrightArray, hkeepArrays⟩);
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
    (refine Light.Ends.setToThen (count h k : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hhead,
                hcountL, count, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hhead, hcountL, count, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hhead, hcountL, count,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
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
          (LightRadixKeys.offset
              (LightReportingPrefixArrays.localCount (512 * h) h) k :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hhead, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
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
          (stageR +
              LightRadixKeys.offset
                (LightReportingPrefixArrays.localCount (512 * h) h) k :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
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
          (stageL +
                LightRadixKeys.offset
                  (LightReportingPrefixArrays.localCount (512 * h) h) k +
              1 :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hhead, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
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
          (stageR +
                LightRadixKeys.offset
                  (LightReportingPrefixArrays.localCount (512 * h) h) k +
              1 :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
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
    (refine Light.Ends.setToThen (k * h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hkhWord,
                hkhWordZ, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hkhWord, hkhWordZ, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hkhWord, hkhWordZ,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepArrays i (by omega))
  have hc := (ReportingHostRelocation.meets
    (LightReportingSuffixCatalogSetup.program_meets (d := d+1) (μ := μ₁)
      (block_fit hk) (preL h J k) (preR h J k) f g hw hcut hboxCut hwidth hn
      (hdataL.trans (by omega)) (hdataR.trans (by omega)) hprefixEndL hprefixEndR hptr hbox hmasks
      hspace hword hvalueWord
      (by intro i hi; exact preL_card hk (by rwa [← count_eq_length]))
      (by intro i hi; exact preR_card hk (by rwa [← count_eq_length]))
      hpre hpre hf hg hstoredL₁ hstoredR₁ (readL hk hleftArray) (readR hk hrightArray) (by omega))
    LightReportingPrefixArrays.program).append [body 10 42]
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
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, count,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [count, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, count,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result μ₂ ⟨hptrs, hboxes, hsourceL, hsourceR, hkeepCatalog⟩);
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
        Light.Ends.setToThen
          (stageL +
              LightRadixKeys.offset
                (LightReportingPrefixArrays.localCount (512 * h) h) k :
            ℕ)
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hhead, LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hhead,
                LightReportingPrefixArrays.time,
                LightReportingSuffixCatalogSetup.time] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine ⟨by simp,hptrs,hboxes,hsourceL,hsourceR,?_,?_,?_,?_⟩
  · exact (hkeepCatalog _ (by omega)).trans hcountL
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (readL hk hleftArray i hi)
  · intro i hi
    exact (hkeepCatalog _ (by omega)).trans (readR hk hrightArray i hi)
  · intro i hi
    exact (hkeepCatalog i (by omega)).trans (hkeepArrays i hi)

end ThreeSum.LightReportingPrefixCatalog

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int}
  {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase work B D d : Nat}
  (hk : @LE.le.{0} Nat instLENat k J)
  (f g :
    Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))) →
      Int),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat cut
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
      @LE.le.{0} Nat instLENat boxCut
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
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
                  cut)))
            srcS →
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
                    cut)))
              srcS →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcS
                  ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h).choose
                    h))
                pairL →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairL
                    (ThreeSum.LightReportingPrefixArrays.localCount
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                      h))
                  pairR →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairR
                      (ThreeSum.LightReportingPrefixArrays.localCount
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                        h))
                    stageL →
                  @LE.le.{0} Nat instLENat
                      (ThreeSum.LightRadixKeys.space stageL
                        (ThreeSum.LightReportingPrefixArrays.localCount
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                          h)
                        k)
                      stageR →
                    @LE.le.{0} Nat instLENat
                        (ThreeSum.LightRadixKeys.space stageR
                          (ThreeSum.LightReportingPrefixArrays.localCount
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                            h)
                          k)
                        ptrBase →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ptrBase
                            (ThreeSum.LightReportingPrefixCatalog.count h k))
                          boxBase →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) boxBase
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (ThreeSum.LightReportingPrefixCatalog.count h k)
                                (ThreeSum.LightReportingSuffixCatalog.stride
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                  boxCut)))
                            maskBase →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
                                (ThreeSum.SubsetAddress.downsetCap
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                  boxCut))
                              work →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                lim.space →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (ThreeSum.LightPascal.tableSize
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  lim.space →
                                @LE.le.{0} Int Int.instLEInt
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    lim.word →
                                  @LE.le.{0} Int Int.instLEInt
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (ThreeSum.LightRadixKeys.word
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                          k))
                                      lim.word →
                                    @LE.le.{0} Int Int.instLEInt
                                        (@Nat.cast.{0} Int instNatCastInt
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                    h))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                        lim.word →
                                      @LE.le.{0} Int Int.instLEInt
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J k)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                    h)))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J
                                                        k)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)))
                                                  B)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J
                                                        k)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)))
                                                  D))))
                                          lim.word →
                                        @LE.le.{0} Nat instLENat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k h)
                                              boxCut)
                                            cut →
                                          (∀
                                              (S :
                                                Finset.{0}
                                                  (Fin
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)))),
                                              @LE.le.{0} Nat instLENat
                                                  (@Finset.card.{0}
                                                    (Fin
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                            (instOfNatNat (nat_lit 512)))
                                                          h)))
                                                    S)
                                                  cut →
                                                @LE.le.{0} Int Int.instLEInt
                                                  (@abs.{0} Int instLatticeInt Int.instAddGroup (f S))
                                                  (@Nat.cast.{0} Int instNatCastInt B)) →
                                            (∀
                                                (S :
                                                  Finset.{0}
                                                    (Fin
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                            (instOfNatNat (nat_lit 512)))
                                                          h)))),
                                                @LE.le.{0} Nat instLENat
                                                    (@Finset.card.{0}
                                                      (Fin
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          J
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                              (instOfNatNat (nat_lit 512)))
                                                            h)))
                                                      S)
                                                    cut →
                                                  @LE.le.{0} Int Int.instLEInt
                                                    (@abs.{0} Int instLatticeInt Int.instAddGroup (g S))
                                                    (@Nat.cast.{0} Int instNatCastInt D)) →
                                              @ThreeSum.LightZetaStages.StoredThrough
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h))
                                                  μ baseL cut f
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h)) →
                                                @ThreeSum.LightZetaStages.StoredThrough
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h))
                                                    μ baseR cut g
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)) →
                                                  @LE.le.{0} Nat instLENat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) d
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                (instOfNatNat (nat_lit 512)))
                                                              h))
                                                          k)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                                      lim.depth →
                                                    @LE.le.{0} Nat instLENat
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) d
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat) J
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                  (instOfNatNat (nat_lit 512)))
                                                                h)))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 14)
                                                            (instOfNatNat (nat_lit 14))))
                                                        lim.depth →
                                                      Light.Meets lim ThreeSum.LightReportingPrefixCatalog.program
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                                                        d
                                                        (@List.cons.{0} Int
                                                          (@HMul.hMul.{0, 0, 0} Int Int Int
                                                            (@instHMul.{0} Int Int.instMul)
                                                            (@Nat.cast.{0} Int instNatCastInt J)
                                                            (@HMul.hMul.{0, 0, 0} Int Int Int
                                                              (@instHMul.{0} Int Int.instMul)
                                                              (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                                (@instOfNat (nat_lit 512)))
                                                              (@Nat.cast.{0} Int instNatCastInt h)))
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt boxCut)
                                                              (@List.cons.{0} Int
                                                                (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                  (@instHMul.{0} Int Int.instMul)
                                                                  (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                    (@instHSub.{0} Int Int.instSub)
                                                                    (@Nat.cast.{0} Int instNatCastInt J)
                                                                    (@Nat.cast.{0} Int instNatCastInt k))
                                                                  (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                    (@instHMul.{0} Int Int.instMul)
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                                      (@instOfNat (nat_lit 512)))
                                                                    (@Nat.cast.{0} Int instNatCastInt h)))
                                                                (@List.cons.{0} Int
                                                                  (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                    (@instHMul.{0} Int Int.instMul)
                                                                    (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                      (@instHSub.{0} Int Int.instSub)
                                                                      (@Nat.cast.{0} Int instNatCastInt J)
                                                                      (@Nat.cast.{0} Int instNatCastInt k))
                                                                    (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                      (@instHMul.{0} Int Int.instMul)
                                                                      (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                                        (@instOfNat (nat_lit 512)))
                                                                      (@Nat.cast.{0} Int instNatCastInt h)))
                                                                  (@List.cons.{0} Int
                                                                    (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                      (@instHMul.{0} Int Int.instMul)
                                                                      (@Nat.cast.{0} Int instNatCastInt k)
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                                          (@instOfNat (nat_lit 512)))
                                                                        (@Nat.cast.{0} Int instNatCastInt h)))
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt baseL)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt baseR)
                                                                        (@List.cons.{0} Int
                                                                          (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                            (@instHMul.{0} Int Int.instMul)
                                                                            (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                                              (@instOfNat (nat_lit 512)))
                                                                            (@Nat.cast.{0} Int instNatCastInt h))
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt h)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt k)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt srcS)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    pairL)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      pairR)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        stageL)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt stageR)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt ptrBase)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt boxBase)
                                                                                            (@List.cons.{0} Int
                                                                                              (@Nat.cast.{0} Int
                                                                                                instNatCastInt maskBase)
                                                                                              (@List.cons.{0} Int
                                                                                                (@Nat.cast.{0} Int
                                                                                                  instNatCastInt work)
                                                                                                (@List.nil.{0}
                                                                                                  Int)))))))))))))))))))))
                                                        μ (ThreeSum.LightReportingPrefixCatalog.time h J k boxCut)
                                                        fun (r : Int) (μ' : Nat → Int) =>
                                                        And
                                                          (@Eq.{1} Int r
                                                            (@Nat.cast.{0} Int instNatCastInt
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) stageL
                                                                (ThreeSum.LightRadixKeys.offset
                                                                  (ThreeSum.LightReportingPrefixArrays.localCount
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                        (instOfNatNat (nat_lit 512)))
                                                                      h)
                                                                    h)
                                                                  k))))
                                                          (And
                                                            (Light.SegN μ' ptrBase
                                                              (@List.ofFn.{0} Nat
                                                                (ThreeSum.LightReportingPrefixCatalog.count h k)
                                                                fun
                                                                  (i :
                                                                    Fin
                                                                      (ThreeSum.LightReportingPrefixCatalog.count h
                                                                        k)) =>
                                                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) boxBase
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@Fin.val
                                                                      (ThreeSum.LightReportingPrefixCatalog.count h k)
                                                                      i)
                                                                    (ThreeSum.LightReportingSuffixCatalog.stride
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                          (@instHSub.{0} Nat instSubNat) J k)
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h))
                                                                      boxCut))))
                                                            (And
                                                              (∀ (i : Nat),
                                                                @LT.lt.{0} Nat instLTNat i
                                                                    (ThreeSum.LightReportingPrefixCatalog.count h k) →
                                                                  @ThreeSum.LightBoxStages.StoredThrough
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                        (@instHSub.{0} Nat instSubNat) J k)
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                          (instOfNatNat (nat_lit 512)))
                                                                        h))
                                                                    μ'
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) boxBase
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) i
                                                                        (ThreeSum.LightReportingSuffixCatalog.stride
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat)
                                                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                              (@instHSub.{0} Nat instSubNat) J k)
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat)
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                                (instOfNatNat (nat_lit 512)))
                                                                              h))
                                                                          boxCut)))
                                                                    boxCut
                                                                    (@ThreeSum.ReportingHostSuffix.leafWeight
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) J
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h))
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                          (@instHSub.{0} Nat instSubNat) J k)
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h))
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) k
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h))
                                                                      (@ThreeSum.ReportingHostSuffix.block_fit J
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h)
                                                                        k hk)
                                                                      f g
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                          (@instHSub.{0} Nat instSubNat) J k)
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                            (instOfNatNat (nat_lit 512)))
                                                                          h))
                                                                      (ThreeSum.ReportingHostPrefixOrder.preL h J k i)
                                                                      (ThreeSum.ReportingHostPrefixOrder.preR h J k i))
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                        (@instHSub.{0} Nat instSubNat) J k)
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                          (instOfNatNat (nat_lit 512)))
                                                                        h)))
                                                              (And
                                                                (@ThreeSum.LightZetaStages.StoredThrough
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat) J
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                        (instOfNatNat (nat_lit 512)))
                                                                      h))
                                                                  μ' baseL cut f
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat) J
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                        (instOfNatNat (nat_lit 512)))
                                                                      h)))
                                                                (And
                                                                  (@ThreeSum.LightZetaStages.StoredThrough
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) J
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                          (instOfNatNat (nat_lit 512)))
                                                                        h))
                                                                    μ' baseR cut g
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) J
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                          (instOfNatNat (nat_lit 512)))
                                                                        h)))
                                                                  (And
                                                                    (@Eq.{1} Int
                                                                      (μ'
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) stageL
                                                                          (ThreeSum.LightRadixKeys.offset
                                                                            (ThreeSum.LightReportingPrefixArrays.localCount
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat)
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                                  (instOfNatNat (nat_lit 512)))
                                                                                h)
                                                                              h)
                                                                            k)))
                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                        (ThreeSum.LightReportingPrefixCatalog.count h
                                                                          k)))
                                                                    (And
                                                                      (∀ (i : Nat),
                                                                        @LT.lt.{0} Nat instLTNat i
                                                                            (ThreeSum.LightReportingPrefixCatalog.count
                                                                              h k) →
                                                                          @Eq.{1} Int
                                                                            (μ'
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat)
                                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                                    stageL
                                                                                    (ThreeSum.LightRadixKeys.offset
                                                                                      (ThreeSum.LightReportingPrefixArrays.localCount
                                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat
                                                                                          Nat
                                                                                          (@instHMul.{0} Nat instMulNat)
                                                                                          (@OfNat.ofNat.{0} Nat
                                                                                            (nat_lit 512)
                                                                                            (instOfNatNat
                                                                                              (nat_lit 512)))
                                                                                          h)
                                                                                        h)
                                                                                      k))
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                    (instOfNatNat (nat_lit 1))))
                                                                                i))
                                                                            (@Nat.cast.{0} Int instNatCastInt
                                                                              (@ThreeSum.SubsetAddress.subsetMask
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat) J
                                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHMul.{0} Nat instMulNat)
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                                      (instOfNatNat (nat_lit 512)))
                                                                                    h))
                                                                                (ThreeSum.ReportingHostPrefixOrder.preL
                                                                                  h J k i))))
                                                                      (And
                                                                        (∀ (i : Nat),
                                                                          @LT.lt.{0} Nat instLTNat i
                                                                              (ThreeSum.LightReportingPrefixCatalog.count
                                                                                h k) →
                                                                            @Eq.{1} Int
                                                                              (μ'
                                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                                      stageR
                                                                                      (ThreeSum.LightRadixKeys.offset
                                                                                        (ThreeSum.LightReportingPrefixArrays.localCount
                                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat
                                                                                            Nat
                                                                                            (@instHMul.{0} Nat
                                                                                              instMulNat)
                                                                                            (@OfNat.ofNat.{0} Nat
                                                                                              (nat_lit 512)
                                                                                              (instOfNatNat
                                                                                                (nat_lit 512)))
                                                                                            h)
                                                                                          h)
                                                                                        k))
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                      (instOfNatNat (nat_lit 1))))
                                                                                  i))
                                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                                (@ThreeSum.SubsetAddress.subsetMask
                                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHMul.{0} Nat instMulNat) J
                                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                      (@instHMul.{0} Nat instMulNat)
                                                                                      (@OfNat.ofNat.{0} Nat
                                                                                        (nat_lit 512)
                                                                                        (instOfNatNat (nat_lit 512)))
                                                                                      h))
                                                                                  (ThreeSum.ReportingHostPrefixOrder.preR
                                                                                    h J k i))))
                                                                        (Light.Kept μ μ' srcS)))))))) := by
  exact @ThreeSum.LightReportingPrefixCatalog.program_meets_sourceProof

#print axioms solution
