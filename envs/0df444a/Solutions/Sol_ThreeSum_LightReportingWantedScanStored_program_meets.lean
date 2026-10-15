-- Prove2me | solution 1 for ThreeSum.LightReportingWantedScanStored.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:51:09.982699+00:00
-- url     : https://prove2.me/submissions/09f13a70-4a67-4d8b-b2bd-3aa539b35759

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_DenseGuardWanted_pair_indices_injective
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_incidence_length_le_magnitude
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_persistent_ends
import Theorems.Thm_ThreeSum_LightReportingWantedDispatchStored_program_meets
import Theorems.Thm_ThreeSum_LightReportingWantedScan_program_meets
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_representations_card_le
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_output_count_le_magnitude
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le
import Theorems.Thm_ThreeSum_WantedRecordOrder_label_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
namespace ThreeSumApsp
end ThreeSumApsp

section


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/

/-- A multiple of a positive modulus strictly between its two nearest
nonzero multiples must vanish. -/
theorem eq_zero_of_dvd_of_bounds {R x : ℤ} (hR : 0 < R)
    (hlo : -R < x) (hhi : x < R) (hdiv : R ∣ x) : x = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  by_cases hq : q = 0
  · simp [hq]
  have hcases : q ≤ -1 ∨ 1 ≤ q := by omega
  rcases hcases with hq | hq
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith




































/-- Distinct signed lifts of a fixed A residue never give the same radix
query key under the range guard. -/
theorem guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : SmallLift j) (hk : SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ (j - k) * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < (j - k) * P ∧ (j - k) * P < R := by
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · omega




















































/-! ## The weighted false-count identity -/















































































































































/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

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
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}














































































































































































































































/-! ## The selected local prime and its actual finite schedule -/














































theorem local_representation_cap (h : ℕ) (w : Weight (512 * h) (LocalField h))
    (target : LocalField h × LocalField h) :
    hitCount (512 * h) h (localBucketCap h) w target ≤ localBucketCap h ^ 2 :=
  hitCount_cap _ _ _


















end ThreeSum.LocalHashMoments

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






































theorem retained_survives {h : ℕ} (c : RetainedChoice h) :
    Survives h (occurrence c) (edge c) := c.property






theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]
















theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (localPrime h : ℤ) ∣ a - rawHash w s ↔
      HashFamily.hashValue w s = (a : LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, rawHash_cast, sub_eq_zero]
  exact eq_comm







theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : RetainedChoice h) :
    c ∈ Radix.localFiber (localPrime h) rawLeft rawRight a b ↔
      HashFamily.hashValue (mapAt h (occurrence c)) (left (edge c)) = (a : LocalField h) ∧
      HashFamily.hashValue (mapAt h (occurrence c)) (right (edge c)) = (b : LocalField h) := by
  simp only [Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rawLeft, rawRight, dvd_sub_rawHash_iff]
















set_option maxHeartbeats 1000000 in
private theorem occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : Occurrence h) :
    ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
      (fun c => occurrence c = i)).card ≤ localBucketCap h ^ 2 := by
  let hits : Finset (Edge (512 * h) h) := Finset.univ.filter fun e =>
    mapAt h i ∈ HashFamily.trimmedPairEvent (left e) (right e)
      (a : LocalField h) (b : LocalField h)
      (leftVertices (512 * h) h) (rightVertices (512 * h) h) (localBucketCap h)
  have hcount : ((Radix.localFiber (localPrime h) rawLeft rawRight a b :
      Finset (RetainedChoice h)).filter (fun c => occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := retained_survives c
      simp only [Survives, hi, ha, hb] at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hs⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hi] using And.intro ha hb⟩
    · intro c hc d hd he
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
      · exact he
  exact hcount.trans (local_representation_cap h (mapAt h i) (a, b))

/-- The exact local cap counts map occurrences separately, including
repetitions in the chosen greedy schedule. -/
theorem localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).card ≤
      scheduleSize h * localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : Occurrence h,
        ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
          (fun c => occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Occurrence h, localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact occurrence_fiber_bound h a b i
    _ = _ := by simp [Occurrence]





















theorem representations_card_bound (h J : ℕ) (a b : ℤ) :
    (representations h J a b).card ≤ representationCap h J :=
  Radix.representations_card_le (localPrime h) rawLeft rawRight
    (scheduleSize h * localBucketCap h ^ 2) (localFiber_card_bound h) J a b


















































































































end ThreeSum.GlobalEncoding

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds



theorem lift_small (j : Fin 3) : Arithmetic.SmallLift (lift j) := by
  fin_cases j <;> simp [lift, Arithmetic.SmallLift]

theorem lift_injective : Function.Injective lift := by
  intro i j hij
  apply Fin.ext
  unfold lift at hij
  omega













































































































theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by
  simp only [witnesses, Finset.mem_filter, Finset.mem_univ, true_and]











































/-- Projection to the retained list is injective on the raw witnesses of
one original triple: the guard makes its lift unique. -/
theorem witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    Set.InjOn (fun w : Witness h J => List.ofFn w.1) (witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (mem_witnesses.mp hw).2
  have hvq := (mem_witnesses.mp hv).2
  have hd : globalModulus h J ∣
      (a % P + lift w.2 * P + d) - (a % P + lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := Arithmetic.guarded_lift_unique hP hguard (lift_small w.2) (lift_small v.2) hd
  exact Prod.ext ht (lift_injective hj)

theorem witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).card ≤ representationCap h J := by
  calc
    _ ≤ (representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Witness h J => List.ofFn w.1)
      · intro w hw
        exact (mem_witnesses.mp hw).1
      · exact witness_projection_injective hP hguard
    _ ≤ _ := representations_card_bound h J (b % P) (c % P + d)






























section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma



















































theorem rawMass_eq_sum_witnesses (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d T a b c =
      ∑ t ∈ T, (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card :=
  Finset.card_sigma _ _
















































































































































end OriginalIndices

end ThreeSum.RawIncidences

end

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩
















































end ThreeSum.BandRawA

end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/
















/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩








/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



































































theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩
























































end ThreeSum.BandRawA

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]






























































































end ThreeSum.BandRawA

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000


























@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by
  simp only [finiteAIndices,mem_filter,mem_univ,true_and]





@[simp] theorem mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteOwnerProduct nA nB nC g rs s ↔
      coordinates t ∈ ownerProduct nA nB nC g rs s := by
  simp only [finiteOwnerProduct,ownerProduct,mem_product,mem_finiteAIndices,
    mem_finiteBandPositions,coordinates]

@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]







































































































end ThreeSum.BandRawA

end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

























variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

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

































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




theorem rootMass_eq {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) :
    rootMass I w=(domain I w).card := by
  simp [rootMass,prefixQuery,Reporting.mass,Subset.fiberMass]












































































end ThreeSum.ReportingHostFrontierLayout

end

section


/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]




@[simp] theorem mass_nil {h J : ℕ} (I : Finset (RawItem h J α β γ)) : mass I []=0 := rfl

theorem mass_append {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (w : Wanted h J α) :
    mass I (visited++[w])=mass I visited+rootMass I w := by simp [mass]

theorem mass_le_raw_card {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (hn : visited.Nodup) : mass I visited ≤ I.card := by
  unfold mass
  rw [← List.sum_toFinset _ hn]
  calc
    _ ≤ ∑ w : Wanted h J α, rootMass I w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = I.card := by
      simp only [rootMass_eq]
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)



































end ThreeSum.DenseGuard

end

section


/-!
# Owner queries are the exact fibers of the global physical domain

The A incidence fixes its owner. Restricting to that owner's B/C bands
therefore leaves the entire wanted fiber unchanged. The mass read by the
owner-local query is exactly the mass charged by the global dense guard.
-/

namespace ThreeSum.DenseGuardBands

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

section General

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem domain_eq_of_first_fiber {h J : ℕ} {P shift : ℤ}
    (T U : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α)
    (hf : ∀ t : Original α β γ, t.1=w.1 → (t ∈ T ↔ t ∈ U)) :
    domain (rawOn h J P shift T a b c) w=domain (rawOn h J P shift U a b c) w := by
  ext r
  simp only [domain,mem_filter,mem_rawOn]
  constructor
  · rintro ⟨⟨ht,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mp ht,hr⟩,he⟩
  · rintro ⟨⟨hu,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mpr hu,hr⟩,he⟩

end General

open BandRawA

theorem finite_owner_fiber {nA nB nC g s : ℕ} {rs : List BandCandidateRows.Record}
    (hs : s < rs.length) (i : Fin (items nA g rs).length)
    (hi : (BandRawA.labelAt nA g rs i.val).owner=s)
    (t : Fin (items nA g rs).length × Fin nB × Fin nC) (ht : t.1=i) :
    t ∈ finiteAllProducts nA nB nC g rs ↔ t ∈ finiteOwnerProduct nA nB nC g rs s := by
  have ho : (BandRawA.labelAt nA g rs t.1.val).owner=s := by rw [ht]; exact hi
  simp only [mem_finiteAllProducts,mem_finiteOwnerProduct,mem_allProducts,mem_ownerProduct hs,
    coordinates,ownerRecord,ho,true_and]

theorem domain_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    domain (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      domain (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  domain_eq_of_first_fiber _ _ a b c w (finite_owner_fiber hs w.1 ho)

theorem prefixQuery_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s)
    (pre : List (Finset (Fin (512*h)))) :
    prefixQuery (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w k pre=
      prefixQuery (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w k pre := by
  simp only [prefixQuery,domain_global_eq_owner rs hs a b c w ho]

theorem rootMass_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    rootMass (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      rootMass (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  prefixQuery_global_eq_owner rs hs a b c w ho []

end ThreeSum.DenseGuardBands

end

section


/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder











































theorem labelAt_injective {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift) :
    Function.Injective (labelAt H) := by
  intro k k' he
  have hp := label_injective (output_bounds H k.isLt).1 (output_bounds H k'.isLt).1
    (output_bounds H k.isLt).2 (output_bounds H k'.isLt).2 he
  exact Fin.ext (pair_indices_injective H k.isLt k'.isLt hp.1 hp.2)

























theorem labelAt_mem {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : labelAt H slot ∈ RawAKeyLists.wanted M P xs h J shift := by
  obtain ⟨i,j,hi,_,hL,hR,hm⟩ := WantedRecordCoverage.output_pair H slot.isLt
  simpa only [labelAt,leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using hm











end ThreeSum.DenseGuardWanted

end

section


/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000


















variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩


























































































open Filter













end ThreeSum.ThreeSumColorBudgets

end

section


/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000













theorem records_le_payload (free h J NB NC g : ℕ) :
    records free ≤ payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _












































































end ThreeSum.SharedReportingBankHeader

end

section


/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData

open Light Scales BandScales EncodedColorNormalizedData

attribute [local instance] _root_.ThreeSum.ThreeSumReportingSetupData.instNeZeroNatRadix
































theorem report_le_counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    reportBase free n A B C hsA hsB hsC+9 ≤ counter free n A B C hsA hsB hsC :=
  (SharedReportingBankHeader.records_le_payload ..).trans
    (SharedReportingBankHeader.payload_le_finish ..)






























end ThreeSum.ThreeSumReportingSetupData

end

section


/-!
# A reusable finite scratch layout for every wanted slot

The capacity uses the original physical input counts and the retained
representation cap. Its memory bound does not charge any traversal time:
only the actual retained frontier cells are visited. A mask span of `2^W`
also bounds every partial-depth terminal candidate array.
-/

namespace ThreeSum.ReportingHostWantedLayout

open Finset GlobalEncoding RawIncidences RawReporting LocalCoverBounds
open ReportingHostFrontierLayout LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

























































































section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem raw_card_le {h J : ℕ} {P shift : ℤ}
    (T : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (hP : 0<P) (hg : 4*P≤globalModulus h J) :
    (rawOn h J P shift T a b c).card≤T.card*representationCap h J := by
  change rawMass h J P shift T a b c≤_
  rw [rawMass_eq_sum_witnesses]
  calc
    _ ≤ ∑ _t∈T, representationCap h J := Finset.sum_le_sum (fun _ _ => witnesses_card_bound hP hg)
    _ = _ := by simp

























end Mass

end ThreeSum.ReportingHostWantedLayout

end

section


/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical

open Light BandRawA BandCandidateRows RawIncidences GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000





















theorem transport_injective {α β : Type*} {h J : ℕ} (e : α≃β) :
    Function.Injective (transport (h := h) (J := J) e) := by
  intro w w' he
  exact Prod.ext (e.injective (congrArg (fun z : RawReporting.Wanted h J β => z.1) he))
    (congrArg (fun z : RawReporting.Wanted h J β => z.2) he)






section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P (values f (items n g rs)))
    (LightGuardedWanted.right h J) (3*(values f (items n g rs)).length)
    (LightGuardedWanted.totalKeys h J) shift)




theorem wantedAt_injective : Function.Injective (wantedAt H) :=
  (transport_injective (incidenceIndices f n g rs)).comp (DenseGuardWanted.labelAt_injective H)

theorem wantedAt_position (slot : Fin (μ free).toNat) :
    (wantedAt H slot).1.val=
      DenseGuardWanted.leftIndex μ free (3*(items n g rs).length)
        (LightGuardedWanted.totalKeys h J) M slot.val%(items n g rs).length := by
  simp only [wantedAt,transport,incidenceIndices,DenseGuardWanted.labelAt,
    WantedRecordOrder.label,values_length,Equiv.coe_fn_mk]







theorem wantedAt_output (slot : Fin (μ free).toNat) :
    (wantedAt H slot).2.2=LightOutputDecodeOriginal.output h J
      (DenseGuardWanted.rightIndex μ free (3*(items n g rs).length)
        (LightGuardedWanted.totalKeys h J) M slot.val) := by
  simp only [wantedAt,transport,DenseGuardWanted.labelAt,WantedRecordOrder.label,values_length]









theorem wantedAt_key (slot : Fin (μ free).toNat) :
    (M : ℤ) ∣ valueAt n g rs f (wantedAt H slot).1.val%(P : ℤ)+
      lift (wantedAt H slot).2.1*(P : ℤ)+shift-globalKey (wantedAt H slot).2.2 := by
  exact RawAKeyLists.mem_wanted.mp (DenseGuardWanted.labelAt_mem H slot)

































end Actual

end ThreeSum.ReportingHostWantedPhysical

end

section


/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000





































theorem owner_lt {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    owner rs w<rs.length := (at_bounds w.1.isLt).1











theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    rootMass (globalItems h J n NB NC g p rs fA fB fC shift) w=
      rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w :=
  DenseGuardBands.rootMass_global_eq_owner rs (owner_lt rs w) _ _ _ w rfl














































section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)
























end Actual

end ThreeSum.ReportingHostWantedOriginal

end

section


/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset
open scoped BigOperators






theorem prefixMass_zero (mass : ℕ → ℕ) : prefixMass mass 0=0 := by simp [prefixMass]

theorem prefixMass_succ (mass : ℕ → ℕ) (n : ℕ) :
    prefixMass mass (n+1)=prefixMass mass n+mass n := by
  simp only [prefixMass,sum_range_succ]



























































end ThreeSum.SharedTraversalCosts

end

section


/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical ReportingHostWantedOriginal
open ReportingHostFrontierLayout SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)



theorem labels_nodup : (labels H).Nodup :=
  List.nodup_ofFn_ofInjective (wantedAt_injective H)

theorem prefix_nodup (k : ℕ) : ((labels H).take k).Nodup := (labels_nodup H).take

theorem prefix_step (i : Fin (μ free).toNat) :
    (labels H).take (i.val+1)=(labels H).take i.val++[wantedAt H i] := by
  have hi : i.val<(labels H).length := by simpa only [labels,List.length_ofFn] using i.isLt
  rw [List.take_succ_eq_append_getElem hi]
  simp only [labels,List.getElem_ofFn]







theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    slotMass H fB fC NB NC i.val=
      rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) := by
  simp only [slotMass,dif_pos i.isLt]
  exact (global_local_mass rs fA fB fC shift (wantedAt H i)).symm

theorem prefix_mass_eq (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    prefixMass (slotMass H fB fC NB NC) k=
      DenseGuard.mass (globalItems h J n NB NC g P rs fA fB fC shift) ((labels H).take k) := by
  induction k with
  | zero => simp only [prefixMass_zero,List.take_zero,DenseGuard.mass_nil]
  | succ k ih =>
      let i : Fin (μ free).toNat := ⟨k,by omega⟩
      rw [prefixMass_succ,ih (by omega)]
      rw [show (labels H).take (k+1)=(labels H).take k++[wantedAt H i] from prefix_step H i]
      rw [DenseGuard.mass_append,show slotMass H fB fC NB NC k=
        rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) from slotMass_at H fB fC NB NC i]

theorem prefix_mass_le_card (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    prefixMass (slotMass H fB fC NB NC) k≤
      (globalItems h J n NB NC g P rs fA fB fC shift).card := by
  rw [prefix_mass_eq H fB fC NB NC k hk]
  exact DenseGuard.mass_le_raw_card _ _ (prefix_nodup H k)
















end Actual

end ThreeSum.ReportingHostWantedPrefix

end

section


/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}





























theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N=
      (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)).length :=
  BandRawA.values_length ..

































theorem count_le_product (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ThreeSumWantedHostData.count n A B C hsA hsB hsC≤3*(config free n A B C hsA hsB hsC).N*
      LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)) := by
  have hh := H.countBound
  rw [ThreeSumWantedHostData.count_read H,Int.toNat_natCast] at hh
  exact (Nat.le_mul_of_pos_left _ (radix_pos n)).trans hh




















end ThreeSum.EncodedColorWantedConsumerData

end

section


/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000





variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem kept_counter
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    Kept μ ν (config free n A B C hsA hsB hsC).counter := by
  intro a ha
  have he : (config free n A B C hsA hsB hsC).layoutHeader=
      (config free n A B C hsA hsB hsC).counter+4 := rfl
  exact K a ⟨by omega,Or.inl ha⟩

theorem retained_of_kept
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : Kept μ ν (config free n A B C hsA hsB hsC).counter) :
    EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC := by
  have hbefore := ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  have hsource : EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8≤
      (config free n A B C hsA hsB hsC).counter := by
    change ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC≤
      ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
    omega
  exact ⟨H.of_kept K hsource,SharedReportingBankHeader.Stored.of_kept HQ K le_rfl⟩

theorem retained_of_keptBut
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC :=
  retained_of_kept H HQ (kept_counter K)

theorem metadata_reads_of_keptBut
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    let ctr := (config free n A B C hsA hsB hsC).counter
    ν (ctr+1)=μ (ctr+1) ∧ ν (ctr+2)=μ (ctr+2) ∧ ν (ctr+3)=μ (ctr+3) := by
  have he : (config free n A B C hsA hsB hsC).layoutHeader=
      (config free n A B C hsA hsB hsC).counter+4 := rfl
  exact ⟨K _ ⟨by omega,Or.inr (by omega)⟩,
    K _ ⟨by omega,Or.inr (by omega)⟩,K _ ⟨by omega,Or.inr (by omega)⟩⟩

theorem DenseMetadata.of_keptBut {cap score : ℕ}
    (H : DenseMetadata μ (config free n A B C hsA hsB hsC).counter cap score)
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    DenseMetadata ν (config free n A B C hsA hsB hsC).counter cap score := by
  obtain ⟨h1,h2,h3⟩ := metadata_reads_of_keptBut K
  exact ⟨h1.trans H.1,h2.trans H.2.1,h3.trans H.2.2⟩

theorem initial_dense_metadata
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    DenseMetadata μ (config free n A B C hsA hsB hsC).counter
      (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
      (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) := H.dense.2

end ThreeSum.EncodedColorWantedConsumerData

end

section


/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting GlobalEncoding
open ReportingHostWantedPhysical ReportingHostWantedOriginal ReportingHostWantedPrefix
open LightReportingWantedScan SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)






theorem slotHit_at (fB fC : ℕ→ℤ) (NB NC K : ℕ) (i : Fin (μ free).toNat) :
    slotHit H fB fC NB NC K i.val ↔
      Terminal h J n NB NC g P rs fA fB fC shift (wantedAt H i) K := by
  simp only [slotHit,dif_pos i.isLt]

















































end Actual

end ThreeSum.ReportingHostWantedDecision

end

section


/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem input_le_magnitude (n : ℕ) : n ≤ magnitude n := by
  have hn : n ≤ 2^(inputBits n+1) := by
    simpa only [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))




























































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light GlobalEncoding LocalCoverBounds SharedReportingBankLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
































































































theorem wanted_mass_bound_le {n N NB NC : ℕ}
    (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    massBound N NB NC (representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤3*(magnitude n)^7 := by
  have hb := hB.trans (input_le_magnitude n)
  have hc := hC.trans (input_le_magnitude n)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hb) hc)
    (wanted_representation_cap_le n)
  calc
    _ ≤ ((3*(magnitude n)^3)*magnitude n)*magnitude n*(magnitude n)^2 := hh
    _ = _ := by ring



























end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000






theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (magnitude n)^e≤(magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)











































































































































noncomputable section









































end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical SharedReportingBankResourceBounds
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000





















































variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}










theorem label_position (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    (label H s).1.val=rawIndex μ (config free n A B C hsA hsB hsC) s.val %
      (config free n A B C hsA hsB hsC).N := by
  have hh := wantedAt_position H.wanted (slot H s)
  calc
    (label H s).1.val = _ := hh
    _ = _ := by
      simp only [slot,rawIndex,DenseGuardWanted.leftIndex,config,incidences,values_length]

theorem label_output (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    (label H s).2.2=LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (outputIndex μ (config free n A B C hsA hsB hsC) s.val) := by
  have hh := wantedAt_output H.wanted (slot H s)
  calc
    (label H s).2.2 = _ := hh
    _ = _ := by
      simp only [slot,outputIndex,DenseGuardWanted.rightIndex,config,incidences,values_length,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum.SharedReportingBankResourceBounds.blocks]

theorem slot_indices (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    rawIndex μ (config free n A B C hsA hsB hsC) s.val<3*(config free n A B C hsA hsB hsC).N ∧
      outputIndex μ (config free n A B C hsA hsB hsC) s.val<OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n := by
  exact DenseGuardWanted.output_bounds H.wanted (slot H s).isLt

theorem slot_reads (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    let cfg := config free n A B C hsA hsB hsC
    μ (cfg.pairs+2*s.val)=(rawIndex μ cfg s.val : ℤ) ∧
      μ (cfg.pairs+2*s.val+1)=(outputIndex μ cfg s.val : ℤ) := by
  obtain ⟨i,j,_,_,hi,hj,_⟩ := WantedRecordCoverage.output_pair H.wanted (slot H s).isLt
  change μ ((config free n A B C hsA hsB hsC).pairs+2*s.val)=(i : ℤ) at hi
  change μ ((config free n A B C hsA hsB hsC).pairs+2*s.val+1)=(j : ℤ) at hj
  simp [rawIndex,outputIndex,hi,hj]

theorem label_key (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) ∣
      valueAt A.length (bandSize n) (records n A B C hsA hsB hsC) (fun j => A.getD j 0) (label H s).1.val %
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift (label H s).2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey (label H s).2.2 := by
  have hm : globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)=(radix n : ℤ) := by
    simp only [globalModulus,Scales.radix,Scales.localRadix,Nat.cast_pow,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum.SharedReportingBankResourceBounds.blocks]
  rw [hm]
  exact wantedAt_key H.wanted (slot H s)

end ThreeSum.ReportingHostWantedConsumerData

end

section


/-! # Finite word bounds for every physical wanted mass

Each original triple has at most the established representation cap many
raw witnesses. The incidence coordinate is its physical position, so the
finite product bound retains every owner and every repeated value. The
injective physical wanted labels then bound every scan prefix by the same
global raw cardinality.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Finset Light RawIncidences RawReporting GlobalEncoding
open ReportingHostFrontierLayout ReportingHostWantedLayout
open BandRawA BandCandidateRows ReportingHostWantedOriginal

set_option maxHeartbeats 1900000
set_option maxRecDepth 15000

theorem wanted_finite_raw_card_le {h J N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤globalModulus h J) :
    (rawOn h J P shift T a b c).card≤massBound N NB NC (representationCap h J) := by
  have hc : T.card≤N*NB*NC := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc] using Finset.card_le_univ T
  exact (raw_card_le T a b c hP hguard).trans (Nat.mul_le_mul_right _ hc)

theorem wanted_finite_raw_card_le_magnitude {n N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (rawOn (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) P shift T a b c).card≤3*(magnitude n)^7 :=
  (wanted_finite_raw_card_le T a b c hP hguard).trans (wanted_mass_bound_le hN hB hC)

theorem wanted_global_card_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (globalItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift).card≤3*(magnitude n)^7 :=
  wanted_finite_raw_card_le_magnitude (finiteAllProducts nA NB NC g rs)
    (fun i => valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC

theorem wanted_local_card_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) (AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift w).card≤3*(magnitude n)^7 :=
  wanted_finite_raw_card_le_magnitude (finiteOwnerProduct nA NB NC g rs (owner rs w))
    (fun i => valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC









theorem wanted_local_root_le {n nA NB NC g P : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) (AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    rootMass (localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift w) w≤3*(magnitude n)^7 := by
  rw [rootMass_eq]
  exact (Finset.card_filter_le _ _).trans (wanted_local_card_le rs fA fB fC shift w hP hguard hN hB hC)

section Physical

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n nA NB NC g free P : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime (half n)^blocks n)
    (LightGuardedWanted.left P (values fA (items nA g rs)))
    (LightGuardedWanted.right (half n) (blocks n)) (3*(values fA (items nA g rs)).length)
    (LightGuardedWanted.totalKeys (half n) (blocks n)) shift)

theorem wanted_physical_slot_mass_le (i : ℕ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    ReportingHostWantedPrefix.slotMass H fB fC NB NC i≤3*(magnitude n)^7 := by
  unfold ReportingHostWantedPrefix.slotMass
  split
  · exact wanted_local_root_le rs fA fB fC shift _ hP hguard hN hB hC
  · exact Nat.zero_le _

theorem wanted_physical_prefix_mass_le (k : ℕ) (hk : k≤(μ free).toNat)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (items nA g rs).length≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    SharedTraversalCosts.prefixMass (ReportingHostWantedPrefix.slotMass H fB fC NB NC) k≤3*(magnitude n)^7 :=
  (ReportingHostWantedPrefix.prefix_mass_le_card H fB fC NB NC k hk).trans
    (wanted_global_card_le rs fA fB fC shift hP hguard hN hB hC)

end Physical
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000






theorem wanted_scan_count_le {n N count : ℕ}
    (hN : N≤3*(magnitude n)^3)
    (hcount : count≤(3*N)*LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    count≤wantedScanCount n := by
  have ho : LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤(magnitude n)^2 :=
    output_count_le_magnitude n
  calc
    _ ≤ (3*N)*LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) := hcount
    _ ≤ (9*(magnitude n)^3)*(magnitude n)^2 := Nat.mul_le_mul (by omega) ho
    _ = wantedScanCount n := by unfold wantedScanCount; ring

theorem wanted_scan_count_envelope (n : ℕ) : wantedScanCount n+4≤wantedEnvelope n := by
  have h5 := wanted_power_le n 5 10 (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedScanCount wantedEnvelope
  omega

theorem wanted_scan_step_of_ok {lim : Limits} {n U dst d count : ℕ}
    (hcount : count≤wantedScanCount n) (hok : (wantedScanNeed n U).Ok lim dst d) :
    (wantedNeed n U).Ok lim dst (d+count+4) :=
  hok.mono le_rfl le_rfl (by dsimp only [wantedScanNeed]; omega)

theorem wanted_scan_at_depth_of_ok {lim : Limits} {n U dst d count e : ℕ}
    (hcount : count≤wantedScanCount n) (he : e≤d+count+4)
    (hok : (wantedScanNeed n U).Ok lim dst d) : (wantedNeed n U).Ok lim dst e :=
  (wanted_scan_step_of_ok hcount hok).mono le_rfl le_rfl (by omega)








noncomputable section


















end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Frozen physical order and the exact cost of the ascending consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000





variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}



















theorem mass_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    mass H s.val=labelMass n A B C hsA hsB hsC (label H s) := by
  exact (ReportingHostWantedPrefix.slotMass_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length (slot H s)).trans
      (ReportingHostWantedOriginal.global_local_mass (records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) (label H s))

theorem hit_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    hit H s.val ↔ labelHit n A B C hsA hsB hsC (label H s) := by
  exact ReportingHostWantedDecision.slotHit_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (LightSwitchDepth.depth (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (slot H s)

theorem stepTime_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    stepTime H s.val=
      LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
        (recordTime free n A B C hsA hsB hsC (label H s)
          (outputIndex μ (config free n A B C hsA hsB hsC) s.val)
          (prefixMass (mass H) s.val) (threshold n A B C hsA hsB hsC)) := by
  simp only [stepTime,dif_pos s.isLt]

theorem mass_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (i : ℕ) (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    mass H i≤3*(magnitude n)^7 := by
  have hN := incidence_length_le_magnitude H
  rw [incidence_length_eq] at hN
  exact wanted_physical_slot_mass_le H.wanted i hp hg hN
    (ThreeSumColorBudgets.normalized_lengths H).2.1 (ThreeSumColorBudgets.normalized_lengths H).2.2

theorem prefix_mass_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    {k : ℕ} (hk : k≤count n A B C hsA hsB hsC)
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    prefixMass (mass H) k≤3*(magnitude n)^7 := by
  have hN := incidence_length_le_magnitude H
  rw [incidence_length_eq] at hN
  exact wanted_physical_prefix_mass_le H.wanted k
    (by rw [count_read H,Int.toNat_natCast]; exact hk) hp hg hN
    (ThreeSumColorBudgets.normalized_lengths H).2.1 (ThreeSumColorBudgets.normalized_lengths H).2.2

theorem slot_reads_of_keptBut (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC))
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    let cfg := config free n A B C hsA hsB hsC
    ν (cfg.pairs+2*s.val)=(rawIndex μ cfg s.val : ℤ) ∧
      ν (cfg.pairs+2*s.val+1)=(outputIndex μ cfg s.val : ℤ) := by
  let cfg := config free n A B C hsA hsB hsC
  have he : cfg.pairs+2*count n A B C hsA hsB hsC≤cfg.counter := (persistent_ends H).pairs
  have hk := kept_counter K
  have hs := s.isLt
  have hr := slot_reads H s
  exact ⟨(hk _ (by dsimp only [cfg] at *; omega)).trans hr.1,
    (hk _ (by dsimp only [cfg] at *; omega)).trans hr.2⟩

end ThreeSum.ReportingHostWantedConsumerData

end

section


/-!
# Execute the complete original physical wanted array

The invariant preserves the initial physical wanted order, all original
source data and all fixed dense metadata. The mutable counter is exactly
the mass of the ascending executed prefix until the first successful call.
-/

namespace ThreeSum.LightReportingWantedScanStored

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedConsumerData SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 3200000
set_option maxRecDepth 22000
set_option linter.unusedSectionVars false

theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hthreshold : threshold n A B C hsA hsB hsC≤9*(magnitude n)^8)
    (hok : (wantedScanNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    Meets lim LightReportingWantedScan.program 152 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (count n A B C hsA hsB hsC)) μ (scanTime H.encoded)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ LightReportingWantedScan.Accepted (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)) ∧
        LightReportingWantedScan.Counter (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)
          (config free n A B C hsA hsB hsC).counter r ν ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := config free n A B C hsA hsB hsC
  let N := count n A B C hsA hsB hsC
  let Inv := fun ν => KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hcount : N≤wantedScanCount n :=
    wanted_scan_count_le (incidence_length_le_magnitude H.encoded) (count_le_product H.encoded)
  have hspace : N+1≤lim.space := by
    have henv := wanted_scan_count_envelope n
    have hh := hok.cells
    change cfg.layoutHeader+wantedEnvelope n≤lim.space at hh
    omega
  have hD : d+N+1≤lim.depth := by
    have hh := hok.depth
    change d+(wantedEnvelope n+wantedScanCount n+4)≤lim.depth at hh
    omega
  have hstep : ∀ i<N, ∀ ν, ∀ e, e+i≤d+N+1 → Inv ν →
      ν cfg.counter=(prefixMass (mass H.encoded) i : ℤ) →
      Meets lim LightReportingWantedDispatch.program 151 e (LightReportingWantedDispatch.arguments cfg i)
        ν (stepTime H.encoded i)
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ threshold n A B C hsA hsB hsC<prefixMass (mass H.encoded) i+mass H.encoded i ∨ hit H.encoded i) ∧
          ξ cfg.counter=((prefixMass (mass H.encoded) i+mass H.encoded i : ℕ) : ℤ) ∧
          Inv ξ ∧ KeptBut ν ξ cfg.layoutHeader cfg.counter 1) := by
    intro i hi ν e he hInv hcounter
    let s : Fin (count n A B C hsA hsB hsC) := ⟨i,hi⟩
    obtain ⟨Hν,HQν⟩ := retained_of_keptBut H.encoded H.catalog hInv
    have hmeta := (initial_dense_metadata H).of_keptBut hInv
    have hindices := slot_indices H.encoded s
    have hreads := slot_reads_of_keptBut H.encoded s hInv
    have hneed : (wantedNeed n U).Ok lim cfg.layoutHeader (e+1) :=
      wanted_scan_at_depth_of_ok hcount (by omega) hok
    have hmass : labelMass n A B C hsA hsB hsC (label H.encoded s)≤3*(magnitude n)^7 := by
      rw [← mass_at H.encoded s]
      exact mass_le H.encoded i hp hg
    have hrun := LightReportingWantedDispatchStored.program_meets (d := e) Hν HQν hx (label H.encoded s)
      hi hindices.1 hindices.2 (label_position H.encoded s) (label_output H.encoded s)
      hreads.1 hreads.2 hp hg (label_key H.encoded s) hcounter hmeta.1 hmeta.2.1
      (prefix_mass_le H.encoded hi.le hp hg) hmass hthreshold hneed
    let QR := fun (r : ℤ) ξ => (r=0 ∨ r=1) ∧
      (r=1 ↔ threshold n A B C hsA hsB hsC<prefixMass (mass H.encoded) i+mass H.encoded i ∨ hit H.encoded i) ∧
      ξ cfg.counter=((prefixMass (mass H.encoded) i+mass H.encoded i : ℕ) : ℤ) ∧
      Inv ξ ∧ KeptBut ν ξ cfg.layoutHeader cfg.counter 1
    have hrun' := hrun.mono (R' := QR) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,?_,?_,?_,hr.2.2.2⟩
      · simpa only [← mass_at H.encoded s,← hit_at H.encoded s,s,threshold,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum.SharedReportingBankResourceBounds.blocks] using hr.2.1
      · simpa only [← mass_at H.encoded s] using hr.2.2.1
      · exact hInv.trans hr.2.2.2)
    have ht := stepTime_at H.encoded s
    change stepTime H.encoded i = _ at ht
    rw [ht]
    exact hrun'
  have hscan := LightReportingWantedScan.program_meets (C := cfg) (mass := mass H.encoded)
    (hit := hit H.encoded) (stepTime := stepTime H.encoded) (Inv := Inv)
    (threshold := threshold n A B C hsA hsB hsC) (n := N) (N := N) (D := d+N) (d := d)
    hok.space hspace hD le_rfl le_rfl SameOn.refl H.dense.1 hstep
  exact hscan.mono le_rfl (fun r ν hr => ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.2⟩)























end ThreeSum.LightReportingWantedScanStored

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {free n U d : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U))
  (hp :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))
  (hg :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hthreshold :
    @LE.le.{0} Nat instLENat (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
  (hok :
    (ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim
      (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader d),
  Light.Meets lim ThreeSum.LightReportingWantedScan.program
    (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) d
    (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
    μ
    (@ThreeSum.ReportingHostWantedConsumerData.scanTime μ free n color x A B C hsA hsB hsC
      (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (ThreeSum.LightReportingWantedScan.Accepted
            (@ThreeSum.ReportingHostWantedConsumerData.mass μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (@ThreeSum.ReportingHostWantedConsumerData.hit μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)))
        (And
          (ThreeSum.LightReportingWantedScan.Counter
            (@ThreeSum.ReportingHostWantedConsumerData.mass μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (@ThreeSum.ReportingHostWantedConsumerData.hit μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter r ν)
          (Light.KeptBut μ ν (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @ThreeSum.LightReportingWantedScanStored.program_meets_sourceProof

#print axioms solution
