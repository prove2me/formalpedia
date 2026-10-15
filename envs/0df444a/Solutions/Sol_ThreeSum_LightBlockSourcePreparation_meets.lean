-- Prove2me | solution 1 for ThreeSum.LightBlockSourcePreparation.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:42:32.910724+00:00
-- url     : https://prove2.me/submissions/b6935c0c-9c19-4961-8203-b56f8100a2cf

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum_BlockIndex_maskHash_left
import Theorems.Thm_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_indices_map
import Theorems.Thm_ThreeSum_LightSourcePreparation_Procs_meets
import Theorems.Thm_ThreeSum_LocalMaskHashes_indexed_bucket_count
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceRowScan
end ThreeSum.LightSourceRowScan
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

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








/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

















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
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]





theorem leftWord_injective : Function.Injective (@leftWord α _) := by
  intro s t he
  ext i
  simpa only [leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [rightWord, decide_eq_decide, not_iff_not] using hi









































section ConcreteGraph

open LayerCounts




variable {L h : ℕ}






















































































































end ConcreteGraph

end ThreeSum.LocalGraph

end

section


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments














































theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]











































































































































































































































end ThreeSum.GlobalEncoding

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












end ThreeSum.MaskErase

end

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by
  simp only [natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [subsetMask, eval_maskOf _ (natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [extend_fin, mem_natPositions]

theorem eval_rawLeft {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,false)).val) (extend fun i => (w (i,true)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.leftWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.leftWord, hi]

theorem eval_rawRight {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,true)).val) (extend fun i => (w (i,false)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.rightWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.rightWord, hi]

end ThreeSum.OneHotMask

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
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds









































@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : Occurrences h J) (i : Fin J) :
    occurrenceIndices o i.val = (o i).val := by
  exact OneHotMask.extend_fin _ i






@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by
  simp only [mapRow,s.isLt,dite_true,OneHotMask.extend_fin]

theorem occurrenceIndices_lt {h J : ℕ} (o : Occurrences h J) {j : ℕ} (hj : j < J) :
    occurrenceIndices o j < scheduleSize h := by
  exact (occurrenceIndices_fin o ⟨j,hj⟩).trans_lt (o ⟨j,hj⟩).isLt

theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < scheduleSize h) (hi : i < 512*h) : mapRow h b s i ≤ localPrime h := by
  rw [mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)

theorem flat_coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) =
      OneHotMask.extend (coefficient o b ∘ (coordEquiv J (512*h)).symm) := by
  unfold flat
  apply congrArg OneHotMask.extend
  funext i
  simp only [occurrenceIndices_fin,mapRow_fin,Function.comp_apply,coefficient]

theorem eval_left {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointLeft o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_left o S

theorem eval_right {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointRight o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_right o S

end ThreeSum.BlockCoefficientRows

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase





theorem bit_subsetMask {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    bit L (SubsetAddress.subsetMask s) j.val = if j ∈ s then 1 else 0 := by
  have h := eraseMask_ne_iff s j
  unfold bit
  split <;> split <;> simp_all





















variable {lim : Limits} {P : Program} {d : ℕ}


























































































end ThreeSum.LightMaskBits

end

section


/-!
# Global mask bits are the exact local block rows

The physical row scan's cardinality and two raw hashes agree with the local
subsets and one-hot words in `BlockEncoding`. This bridge allows independent
trimming to use the selected map's exact retained bucket-count table.
-/

namespace ThreeSum.BlockSourceRows

open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators

set_option maxHeartbeats 1000000




theorem bits_fin {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : Fin L) :
    bits S j i.val = if i ∈ row S j then 1 else 0 := by
  have hh := LightMaskBits.bit_subsetMask (indexSet S) (coordEquiv J L ⟨j,i⟩)
  simpa only [bits,coordEquiv_val,mem_indexSet,mem_row] using hh

theorem count_eq_card {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) :
    count (bits S j) L = (row S j).card := by
  rw [count,← Fin.sum_univ_eq_sum_range]
  have he : row S j = (univ : Finset (Fin L)).filter (fun i => i ∈ row S j) := by
    ext i
    simp
  conv_rhs => rw [he,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  exact bits_fin S j i

theorem hash_eq_eval {L : ℕ} (s : Finset (Fin L)) (b : ℕ → ℕ)
    (w0 w1 : Fin L → ℕ) (hb : ∀ i : Fin L, b i.val = if i ∈ s then 1 else 0) :
    hash b (OneHotMask.extend w0) (OneHotMask.extend w1) L =
      OneHotMask.eval (OneHotMask.extend w0) (OneHotMask.extend w1)
        L (SubsetAddress.subsetMask s) := by
  unfold LightSourceRowScan.hash
  rw [← Fin.sum_univ_eq_sum_range,OneHotMask.eval_subsetMask]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i,OneHotMask.extend_fin,OneHotMask.extend_fin]
  by_cases hmem : i ∈ s <;> simp [hmem]

theorem left_hash {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,false)).val)
      (OneHotMask.extend fun i => (w (i,true)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.leftWord (row S j)) := by
  rw [hash_eq_eval (row S j) (bits S j) _ _ (bits_fin S j),OneHotMask.eval_rawLeft]

theorem right_hash {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,true)).val)
      (OneHotMask.extend fun i => (w (i,false)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.rightWord (row S j)) := by
  rw [hash_eq_eval (row S j) (bits S j) _ _ (bits_fin S j),OneHotMask.eval_rawRight]

end ThreeSum.BlockSourceRows

end

section


/-! # Independent cardinality-and-bucket trimming test -/

namespace ThreeSum.LightSourceFlagTest

open Light




theorem flag_le (card required count cap : ℕ) : flag card required count cap ≤ 1 := by
  unfold flag
  split <;> omega

theorem flag_eq_one (card required count cap : ℕ) :
    flag card required count cap=1 ↔ card=required ∧ count≤cap := by
  unfold flag
  split <;> simp_all








variable {lim : Limits} {P : Program} {d : ℕ}






















end ThreeSum.LightSourceFlagTest

end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h







































































































end ThreeSum.LightResidues

end

section


/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





theorem flag_le (L h p cap : ℕ) (bits w0 w1 hist : ℕ → ℕ) :
    flag L h p cap bits w0 w1 hist ≤ 1 := LightSourceFlagTest.flag_le ..





















variable {lim : Limits} {P : Program} {d : ℕ}



























































































































end ThreeSum.LightSourceRowFlag

end

section


/-! # Conjunction represented by the product of independently computed flags -/

namespace ThreeSum.SourceFlagProduct

open Finset
open scoped BigOperators



@[simp] theorem product_zero (flag : ℕ → ℕ) : product flag 0=1 := by simp [product]

theorem product_succ (flag : ℕ → ℕ) (n : ℕ) :
    product flag (n+1)=product flag n*flag n := Finset.prod_range_succ _ _

theorem product_le {n j : ℕ} (flag : ℕ → ℕ)
    (hflag : ∀ i < n, flag i ≤ 1) (hj : j ≤ n) : product flag j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [product_succ]
    exact (Nat.mul_le_mul (ih (by omega)) (hflag j (by omega))).trans (by decide)

theorem product_eq_one_iff (flag : ℕ → ℕ) (n : ℕ) :
    product flag n=1 ↔ ∀ i < n, flag i=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [product_succ,mul_eq_one,ih]
    constructor
    · rintro ⟨hprev,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hprev i hi
      · exact hn
    · intro hall
      exact ⟨fun i hi => hall i (by omega),hall n (by omega)⟩

theorem product_eq_indicator (flag : ℕ → ℕ) (n : ℕ) (p : Prop) [Decidable p]
    (hflag : ∀ i < n, flag i ≤ 1) (hp : (∀ i < n, flag i=1) ↔ p) :
    product flag n = if p then 1 else 0 := by
  have he := (product_eq_one_iff flag n).trans hp
  have hle := product_le flag hflag le_rfl
  by_cases hh : p
  · simp only [hh,ite_true]
    exact he.mpr hh
  · simp only [hh,ite_false]
    have hn : product flag n≠1 := fun h => hh (he.mp h)
    omega

end ThreeSum.SourceFlagProduct

end

section


/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000






theorem rowFlag_le (L h p cap : ℕ) (sel candidate bits : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (j : ℕ) :
    rowFlag L h p cap sel candidate bits w0 w1 counts j ≤ 1 :=
  LightSourceRowFlag.flag_le ..













































variable {lim : Limits} {P : Program} {d : ℕ}











































































































































































end ThreeSum.LightSourceTrim

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators











































































































theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (choices matrix rows cols t).length = t := Cover.greedyChoices_length ..




end ThreeSum.BooleanGreedy

end

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)




theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1
























































end ThreeSum.LocalMaskGraph

end

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}







theorem count_le (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)






































































































end ThreeSum.LightHistogram

end

section


/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}



















theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]









































































































































end ThreeSum.LightResidueHistogram

end

section


/-!
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes

open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds

variable {h L k : ℕ}















theorem leftCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    leftCode w k i < localPrime h := by
  unfold leftCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem rightCode_lt (w : Weight L (LocalField h)) (k i : ℕ) :
    rightCode w k i < localPrime h := by
  unfold rightCode LightHashHistogram.code
  exact LightResidues.residue_lt (localPrime_pos h) 1 _

theorem leftCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (leftCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i)) := by
  unfold leftCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawLeft,GlobalEncoding.rawHash_cast]

theorem rightCode_cast (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (rightCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.rightWord (setAt L k i)) := by
  unfold rightCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawRight,GlobalEncoding.rawHash_cast]













































theorem left_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.leftWord LocalGraph.leftWord_injective
    (leftCode w k) (fun i _ => leftCode_lt w k i) (fun _ hi => leftCode_cast w hi) hr

theorem right_count (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.rightWord LocalGraph.rightWord_injective
    (rightCode w k) (fun i _ => rightCode_lt w k i) (fun _ hi => rightCode_cast w hi) hr

end ThreeSum.LocalMaskHashes

end

section


/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule

open Finset LocalHashMoments LocalCoverBounds GlobalEncoding











































































theorem indices_length (h : ℕ) : (indices h).length = scheduleSize h :=
  BooleanGreedy.choices_length ..
















theorem candidateAt_lt (h : ℕ) (s : Occurrence h) : candidateAt h s < rows h := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  unfold candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact indices_lt h (List.getElem_mem hs)

theorem candidateAt_mapAt (h : ℕ) (s : Occurrence h) :
    candidate h (candidateAt h s) = mapAt h s := by
  have hs : s.val < (indices h).length := by rw [indices_length]; exact s.isLt
  have hs' : s.val < (localSchedule h).length := by
    rw [← scheduleSize_eq_length]
    exact s.isLt
  have he := congrArg (fun xs : List (Weight (512*h) (LocalField h)) => xs.getD s.val default) (indices_map h)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hs),List.getElem_map,
    List.getD_eq_getElem _ _ hs'] at he
  unfold candidateAt mapAt
  rw [List.getD_eq_getElem _ _ hs]
  exact he

theorem leftCount_candidateAt (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.leftCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.leftCount
  rw [LocalMaskHashes.left_count _ hr,candidateAt_mapAt]

theorem rightCount_candidateAt (h : ℕ) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    LocalCoverMatrix.rightCount (candidate h (candidateAt h s)) h r =
      HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) := by
  unfold LocalCoverMatrix.rightCount
  rw [LocalMaskHashes.right_count _ hr,candidateAt_mapAt]

























end ThreeSum.LightLocalCoverSchedule

end

section


/-!
# Concrete trimming flags equal the original independent endpoint conditions

The exact greedy occurrence-to-candidate bridge connects retained candidate
bucket tables to the unchanged `mapAt` schedule. A product of row flags is
therefore exactly the original `LeftAllowed` or `RightAllowed` condition.
-/

namespace ThreeSum.BlockSourceFlags

open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1200000



@[simp] theorem candidateIndices_fin (h : ℕ) (s : Occurrence h) :
    candidateIndices h s.val = LightLocalCoverSchedule.candidateAt h s := rfl

theorem candidateIndices_lt {h s : ℕ} (hs : s < scheduleSize h) :
    candidateIndices h s < LightLocalCoverSchedule.rows h :=
  LightLocalCoverSchedule.candidateAt_lt h ⟨s,hs⟩










theorem mapRow_extend {h : ℕ} (s : Occurrence h) (b : Bool) :
    mapRow h b s.val = OneHotMask.extend (fun i => (mapAt h s (i,b)).val) := by
  simp only [mapRow,s.isLt,dite_true]

theorem left_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h false) (mapRow h true) (leftCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.leftWord (row S j))) ≤ localBucketCap h := by
  unfold LightSourceTrim.rowFlag LightSourceRowFlag.flag
  rw [occurrenceIndices_fin,candidateIndices_fin]
  change LightSourceFlagTest.flag (LightSourceRowScan.count (BlockSourceRows.bits S j) (512*h)) h
    (leftCount h (LightLocalCoverSchedule.candidateAt h (o j))
      (LightResidues.residue (localPrime h) 1
        (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h false (o j).val)
          (mapRow h true (o j).val) (512*h) : ℤ))) (localBucketCap h) = 1 ↔ _
  rw [LightSourceFlagTest.flag_eq_one,BlockSourceRows.count_eq_card]
  unfold leftCount
  rw [LightLocalCoverSchedule.leftCount_candidateAt h (o j)
    (LightResidues.residue_lt (localPrime_pos h) 1 _)]
  have he : ((LightResidues.residue (localPrime h) 1
      (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h false (o j).val)
        (mapRow h true (o j).val) (512*h) : ℤ) : ℕ) : LocalField h) =
      HashFamily.hashValue (mapAt h (o j)) (LocalGraph.leftWord (row S j)) := by
    rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
      mapRow_extend,mapRow_extend,BlockSourceRows.left_hash,GlobalEncoding.rawHash_cast]
  rw [he]

theorem right_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h true) (mapRow h false) (rightCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.rightWord (row S j))) ≤ localBucketCap h := by
  unfold LightSourceTrim.rowFlag LightSourceRowFlag.flag
  rw [occurrenceIndices_fin,candidateIndices_fin]
  change LightSourceFlagTest.flag (LightSourceRowScan.count (BlockSourceRows.bits S j) (512*h)) h
    (rightCount h (LightLocalCoverSchedule.candidateAt h (o j))
      (LightResidues.residue (localPrime h) 1
        (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h true (o j).val)
          (mapRow h false (o j).val) (512*h) : ℤ))) (localBucketCap h) = 1 ↔ _
  rw [LightSourceFlagTest.flag_eq_one,BlockSourceRows.count_eq_card]
  unfold rightCount
  rw [LightLocalCoverSchedule.rightCount_candidateAt h (o j)
    (LightResidues.residue_lt (localPrime_pos h) 1 _)]
  have he : ((LightResidues.residue (localPrime h) 1
      (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h true (o j).val)
        (mapRow h false (o j).val) (512*h) : ℤ) : ℕ) : LocalField h) =
      HashFamily.hashValue (mapAt h (o j)) (LocalGraph.rightWord (row S j)) := by
    rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
      mapRow_extend,mapRow_extend,BlockSourceRows.right_hash,GlobalEncoding.rawHash_cast]
  rw [he]

theorem left_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h false) (mapRow h true) (leftCount h)) J =
      if LeftAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (left_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (left_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

theorem right_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h true) (mapRow h false) (rightCount h)) J =
      if RightAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (right_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (right_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

end ThreeSum.BlockSourceFlags

end

section


/-!
# All original raw endpoints and independent flags from the actual selected maps

This semantic specialization composes the verified coefficient, endpoint,
row-scan, remainder, bucket lookup, and all-block flag constructions.
-/

namespace ThreeSum.LightBlockSourcePreparation

open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1700000

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_sourceProof {pMain : ℕ} (C : LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work : ℕ}
    (o : Occurrences h J) (sets : ℕ → Finset (Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+5 ≤ lim.depth)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*(512*h)*scheduleSize h ≤ coeff0)
    (hcandidates : candidates+scheduleSize h ≤ coeff0)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : LightSourcePreparation.space work J (512*h) (localPrime h) ≤ lim.space)
    (hword : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ) ≤ lim.word)
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hcandidateRead : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ))
    (hread0 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+a) = (mapRow h false s a : ℤ))
    (hread1 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+512*h+a) = (mapRow h true s a : ℤ))
    (hcountL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ))
    (hcountR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (indexSet (sets i)) : ℤ)) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,occ,maps,candidates,histL,histR,masks,n,
        coeff0,coeff1,rawLeft,rawRight,flags,bitBase,rowOut,work]
      μ (LightSourcePreparation.time n J (512*h) (localPrime h)) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = endpointRight o (sets i)) ∧
        (∀ i < n, ν (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        (∀ i < n, ν (flags+n+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        Kept μ ν coeff0) := by
  have hcandidates' : ∀ s < scheduleSize h, μ (candidates+s) = (candidateIndices h s : ℤ) := by
    intro s hs
    exact hcandidateRead ⟨s,hs⟩
  have hboundL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      leftCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have hboundR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      rightCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have run := C.meets (d := d) (μ := μ) (J := J) (L := 512*h) (h := h)
    (p := localPrime h) (cap := localBucketCap h) (occ := occ) (maps := maps)
    (candidates := candidates) (histL := histL) (histR := histR) (masks := masks) (n := n)
    (coeff0 := coeff0) (coeff1 := coeff1) (rawLeft := rawLeft) (rawRight := rawRight)
    (flags := flags) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    (U := localPrime h) (V := (512*h).choose h) (M := scheduleSize h)
    (K := LightLocalCoverSchedule.rows h)
    (occurrenceIndices o) (candidateIndices h) (fun i => SubsetAddress.subsetMask (indexSet (sets i)))
    (mapRow h false) (mapRow h true) (leftCount h) (rightCount h)
    hw hd (localPrime_pos h) (by omega) hocc hmaps hcandidates hleft hright hmasks hc0 hc1 hrawLeft
    hrawRight hflags hbits hrowOut hspace hword (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs => candidateIndices_lt hs) hoccRead hcandidates' hread0 hread1
    (fun _ hs _ ha => mapRow_le false hs ha) (fun _ hs _ ha => mapRow_le true hs ha)
    hcountL hcountR hboundL hboundR hmaskRead
    (fun i _ => (SubsetAddress.subsetMask_isMask (indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨rawL,rawR,left,right,kept⟩
  exact ⟨fun i hi => (rawL i hi).trans (eval_left o (sets i)),
    fun i hi => (rawR i hi).trans (eval_right o (sets i)),
    fun i hi => (left i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (left_product o (sets i))),
    fun i hi => (right i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (right_product o (sets i))),kept⟩

end ThreeSum.LightBlockSourcePreparation

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourcePreparation.Procs P pMain)
  {μ : Nat → Int}
  {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags bitBase rowOut work : Nat}
  (o : ThreeSum.BlockEncoding.Occurrences h J)
  (sets :
    Nat →
      Finset.{0}
        (ThreeSum.BlockRows.Coord J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        lim.depth →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) coeff0 →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                (ThreeSum.GlobalEncoding.scheduleSize h)))
            coeff0 →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
                (ThreeSum.GlobalEncoding.scheduleSize h))
              coeff0 →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                coeff0 →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (ThreeSum.LightLocalCoverSchedule.rows h) (ThreeSum.LocalCoverBounds.localPrime h)))
                  coeff0 →
                @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks n)
                    coeff0 →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff0
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                      coeff1 →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coeff1
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                        rawLeft →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawLeft n) rawRight →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawRight n) flags →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              bitBase →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                                rowOut →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rowOut
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  work →
                                @LE.le.{0} Nat instLENat
                                    (ThreeSum.LightSourcePreparation.space work J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      (ThreeSum.LocalCoverBounds.localPrime h))
                                    lim.space →
                                  @LE.le.{0} Int Int.instLEInt
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (ThreeSum.LightSourcePreparation.word J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          (ThreeSum.LocalCoverBounds.localPrime h)
                                          (ThreeSum.LocalCoverBounds.localPrime h)
                                          ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                h).choose
                                            h)
                                          (ThreeSum.LocalCoverBounds.localBucketCap h)))
                                      lim.word →
                                    (∀ (j : Nat),
                                        @LT.lt.{0} Nat instLTNat j J →
                                          @Eq.{1} Int
                                            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (@ThreeSum.BlockCoefficientRows.occurrenceIndices h J o j))) →
                                      (∀ (s : ThreeSum.GlobalEncoding.Occurrence h),
                                          @Eq.{1} Int
                                            (μ
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                candidates (@Fin.val (ThreeSum.GlobalEncoding.scheduleSize h) s)))
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (ThreeSum.LightLocalCoverSchedule.candidateAt h s))) →
                                        (∀ (s : Nat),
                                            @LT.lt.{0} Nat instLTNat s (ThreeSum.GlobalEncoding.scheduleSize h) →
                                              ∀ (a : Nat),
                                                @LT.lt.{0} Nat instLTNat a
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h) →
                                                  @Eq.{1} Int
                                                    (μ
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          maps
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                  (instOfNatNat (nat_lit 512)))
                                                                h))
                                                            s))
                                                        a))
                                                    (@Nat.cast.{0} Int instNatCastInt
                                                      (ThreeSum.BlockCoefficientRows.mapRow h Bool.false s a))) →
                                          (∀ (s : Nat),
                                              @LT.lt.{0} Nat instLTNat s (ThreeSum.GlobalEncoding.scheduleSize h) →
                                                ∀ (a : Nat),
                                                  @LT.lt.{0} Nat instLTNat a
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h) →
                                                    @Eq.{1} Int
                                                      (μ
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) maps
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                      (instOfNatNat (nat_lit 512)))
                                                                    h))
                                                                s))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                (instOfNatNat (nat_lit 512)))
                                                              h))
                                                          a))
                                                      (@Nat.cast.{0} Int instNatCastInt
                                                        (ThreeSum.BlockCoefficientRows.mapRow h Bool.true s a))) →
                                            (∀ (k : Nat),
                                                @LT.lt.{0} Nat instLTNat k (ThreeSum.LightLocalCoverSchedule.rows h) →
                                                  ∀ (r : Nat),
                                                    @LT.lt.{0} Nat instLTNat r
                                                        (ThreeSum.LocalCoverBounds.localPrime h) →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) histL
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat) k
                                                                (ThreeSum.LocalCoverBounds.localPrime h)))
                                                            r))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (ThreeSum.BlockSourceFlags.leftCount h k r))) →
                                              (∀ (k : Nat),
                                                  @LT.lt.{0} Nat instLTNat k (ThreeSum.LightLocalCoverSchedule.rows h) →
                                                    ∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r
                                                          (ThreeSum.LocalCoverBounds.localPrime h) →
                                                        @Eq.{1} Int
                                                          (μ
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) histR
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat) k
                                                                  (ThreeSum.LocalCoverBounds.localPrime h)))
                                                              r))
                                                          (@Nat.cast.{0} Int instNatCastInt
                                                            (ThreeSum.BlockSourceFlags.rightCount h k r))) →
                                                (∀ (i : Nat),
                                                    @LT.lt.{0} Nat instLTNat i n →
                                                      @Eq.{1} Int
                                                        (μ
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) masks i))
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@ThreeSum.SubsetAddress.subsetMask
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat) J
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                  (instOfNatNat (nat_lit 512)))
                                                                h))
                                                            (@ThreeSum.BlockIndex.indexSet J
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                                  (instOfNatNat (nat_lit 512)))
                                                                h)
                                                              (sets i))))) →
                                                  Light.Meets lim P pMain d
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                                                      (@List.cons.{0} Int
                                                        (@HMul.hMul.{0, 0, 0} Int Int Int
                                                          (@instHMul.{0} Int Int.instMul)
                                                          (@OfNat.ofNat.{0} Int (nat_lit 512)
                                                            (@instOfNat (nat_lit 512)))
                                                          (@Nat.cast.{0} Int instNatCastInt h))
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                                                          (@List.cons.{0} Int
                                                            (@Nat.cast.{0} Int instNatCastInt
                                                              (ThreeSum.LocalCoverBounds.localPrime h))
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (ThreeSum.LocalCoverBounds.localBucketCap h))
                                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt maps)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt candidates)
                                                                    (@List.cons.{0} Int
                                                                      (@Nat.cast.{0} Int instNatCastInt histL)
                                                                      (@List.cons.{0} Int
                                                                        (@Nat.cast.{0} Int instNatCastInt histR)
                                                                        (@List.cons.{0} Int
                                                                          (@Nat.cast.{0} Int instNatCastInt masks)
                                                                          (@List.cons.{0} Int
                                                                            (@Nat.cast.{0} Int instNatCastInt n)
                                                                            (@List.cons.{0} Int
                                                                              (@Nat.cast.{0} Int instNatCastInt coeff0)
                                                                              (@List.cons.{0} Int
                                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                                  coeff1)
                                                                                (@List.cons.{0} Int
                                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                                    rawLeft)
                                                                                  (@List.cons.{0} Int
                                                                                    (@Nat.cast.{0} Int instNatCastInt
                                                                                      rawRight)
                                                                                    (@List.cons.{0} Int
                                                                                      (@Nat.cast.{0} Int instNatCastInt
                                                                                        flags)
                                                                                      (@List.cons.{0} Int
                                                                                        (@Nat.cast.{0} Int
                                                                                          instNatCastInt bitBase)
                                                                                        (@List.cons.{0} Int
                                                                                          (@Nat.cast.{0} Int
                                                                                            instNatCastInt rowOut)
                                                                                          (@List.cons.{0} Int
                                                                                            (@Nat.cast.{0} Int
                                                                                              instNatCastInt work)
                                                                                            (@List.nil.{0}
                                                                                              Int)))))))))))))))))))))
                                                    μ
                                                    (ThreeSum.LightSourcePreparation.time n J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)
                                                      (ThreeSum.LocalCoverBounds.localPrime h))
                                                    fun (x : Int) (ν : Nat → Int) =>
                                                    And
                                                      (∀ (i : Nat),
                                                        @LT.lt.{0} Nat instLTNat i n →
                                                          @Eq.{1} Int
                                                            (ν
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) rawLeft i))
                                                            (@ThreeSum.BlockEncoding.endpointLeft h J o (sets i)))
                                                      (And
                                                        (∀ (i : Nat),
                                                          @LT.lt.{0} Nat instLTNat i n →
                                                            @Eq.{1} Int
                                                              (ν
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) rawRight i))
                                                              (@ThreeSum.BlockEncoding.endpointRight h J o (sets i)))
                                                        (And
                                                          (∀ (i : Nat),
                                                            @LT.lt.{0} Nat instLTNat i n →
                                                              @Eq.{1} Int
                                                                (ν
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) flags i))
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (@ite.{1} Nat
                                                                    (@ThreeSum.BlockEncoding.LeftAllowed h J o (sets i))
                                                                    (@ThreeSum.BlockEncoding.instDecidableLeftAllowed h
                                                                      J o (sets i))
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                      (instOfNatNat (nat_lit 0))))))
                                                          (And
                                                            (∀ (i : Nat),
                                                              @LT.lt.{0} Nat instLTNat i n →
                                                                @Eq.{1} Int
                                                                  (ν
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) flags n)
                                                                      i))
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    (@ite.{1} Nat
                                                                      (@ThreeSum.BlockEncoding.RightAllowed h J o
                                                                        (sets i))
                                                                      (@ThreeSum.BlockEncoding.instDecidableRightAllowed
                                                                        h J o (sets i))
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1)))
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                        (instOfNatNat (nat_lit 0))))))
                                                            (Light.Kept μ ν coeff0)))) := by
  exact @ThreeSum.LightBlockSourcePreparation.meets_sourceProof

#print axioms solution
