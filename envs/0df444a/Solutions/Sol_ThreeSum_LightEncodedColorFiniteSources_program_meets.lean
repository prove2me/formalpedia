-- Prove2me | solution 1 for ThreeSum.LightEncodedColorFiniteSources.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:08:37.914586+00:00
-- url     : https://prove2.me/submissions/8a175e75-cb15-4e94-9aef-01dd2ce326e2

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Theorems.Thm_ThreeSum_LightEncodedColorSources_program_meets
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum_SourceControlCosts_space_le_encoderCount
import Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_keep


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys

section


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators




































theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < outputCount (512 * h) h := by
  have hlo : 256 ^ (2 * h) ≤ outputCount (512 * h) h := by
    simpa [outputCount, show 256 * (2 * h) = 512 * h by omega] using
      pow_le_choose_mul 256 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

























































































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end

section


/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology






















noncomputable section





















































































































































theorem localLength_pos (h : ℕ) : 0 < localLength h := by
  simp only [localLength, LocalHashMoments.localSchedule_length]
  positivity










































































































































end

end ThreeSum.TrimScales

end

section


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology











theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section

































































































































end

end ThreeSum.BandScales

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
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

end

section


/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end

section


/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



















































































theorem time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000






















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega
















noncomputable section

















































































































































end
end ThreeSum.CostLedger

end

section


/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing

open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds































theorem occurrence_card (h J : ℕ) : Fintype.card (Occurrences h J) = scheduleSize h^J := by
  simp only [Occurrences,Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by
  rw [occurrence_card,scheduleCount,replicatedHalf,localLength,scheduleSize_eq_length]

theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by
  unfold mu totalSize microSize microHalf
  ring




























































end ThreeSum.BlockSourceSharing

end

section


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by
  unfold LightBlockSourceCatalog.count
  rw [← occurrence_card,occurrence_card_eq_scheduleCount]






























































































end ThreeSum.BlockSourceCatalogCosts

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega




















































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000







theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder




































theorem word_mono {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightBlockSourceRetainedHost.word NL NR h J ≤ LightBlockSourceRetainedHost.word NL' NR' h J := by
  have hpl := Nat.mul_le_mul_left (2^(J*(512*h))) hl
  have hpr := Nat.mul_le_mul_left (2^(J*(512*h))) hr
  unfold LightBlockSourceRetainedHost.word LightSourceRetainedStages.word
  omega












































end ThreeSum.SourceBandBankLayout

end

section


/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData

open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs

theorem header_end (free h J : ℕ) : free+20 ≤ LightCoverKeyData.keyEnd free h J :=
  (LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h).trans
    (LightCoverKeyData.afterCover_le_keyEnd free h J)





























end ThreeSum.EncodedColorCoverData

end

section


/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys




theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega

















end ThreeSum.EncodedColorWantedData

end

section


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : typedOutputs n ≤ fullOutputs n := by
  have h := choose_pow_le (256*muZero n) (muZero n) (blockCount (inputBits n))
  have hwidth : blockCount (inputBits n)*(256*muZero n)=256*mu n := by
    unfold mu muZero totalSize
    ring
  have hcut : blockCount (inputBits n)*muZero n=mu n := rfl
  rw [hwidth,hcut] at h
  exact h

theorem four_le_scheduleSize (h : ℕ) : 4 ≤ GlobalEncoding.scheduleSize h := by
  unfold GlobalEncoding.scheduleSize LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : localPrime h ≤ 4*outputCount (512*h) h := by
  have ho : 2^(2*h) ≤ outputCount (512*h) h := by
    by_cases hz : h=0
    · simp [hz,outputCount]
    · exact (concrete_output_gt_pow (by omega)).le
  have hu := localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*outputCount (512*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    BlockSourceEncoding.modulus h J ≤ GlobalEncoding.scheduleSize h^J*
      (J*(512*h)).choose (J*(2*h)) := by
  have hl : localPrime h ≤ GlobalEncoding.scheduleSize h*outputCount (512*h) h :=
    (localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (choose_pow_le (512*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ tableCount n := by
  have hm := modulus_le_global_outputs (microHalf (inputBits n)) (blockCount (inputBits n))
  have hc : blockCount (inputBits n)*(2*microHalf (inputBits n))=mu n := by
    rw [Nat.mul_comm,BlockSourceSharing.cutoff_eq]
  rw [BlockSourceSharing.width_eq,hc] at hm
  change LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*fullOutputs n ≥ _ at hm
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm

theorem bandSize_le_fullOutputs (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))

theorem scheduleCount_pos (n : ℕ) : 0 < scheduleCount n := by
  unfold scheduleCount replicatedHalf
  exact pow_pos (localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : bandCount n*fullOutputs n ≤ encoderCount n := by
  have hs : 1 ≤ scheduleCount n := scheduleCount_pos n
  calc
    _ ≤ bandCount n*scheduleCount n*fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (fullOutputs n) (Nat.mul_le_mul_left (bandCount n) hs)
    _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ encoderCount n := by
  calc
    _ ≤ bandSize n*bandCount n := (bandCount_mul_bounds n).1
    _ ≤ fullOutputs n*bandCount n := Nat.mul_le_mul_right _ (bandSize_le_fullOutputs n)
    _ = bandCount n*fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := bands_outputs_le_encoderCount n
























































end ThreeSum.SourceBandCosts

end

section


/-! # Finite cost of both actual original-band catalogs and empty padding -/

namespace ThreeSum.SourceBandPairCosts

open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData




















theorem tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : tableCount n ≤ encoderCount n := by
  have hb : 0 < bandCount n := by
    have hp := (bandCount_mul_bounds n).1
    by_contra h
    have hz : bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ bandCount n*tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem modulus_le_encoderCount {n : ℕ} (hn : 0 < n) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n :=
  (SourceBandCosts.modulus_le_tableCount n).trans (tableCount_le_encoderCount hn)

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandPair.time NL NR (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+3905)*encoderCount n+3139 := by
  have hl := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNL
  have hr := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNR
  have hm := modulus_le_encoderCount hn
  unfold LightSourceBandPair.time Light.fillTime
  nlinarith















end ThreeSum.SourceBandPairCosts

end

section


/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts

open Scales TrimScales StageBounds CostLedger BandScales

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+5205)*encoderCount n+4859 := by
  have hp := SourceBandPairCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hb := SourceBandBanksCosts.time_le_encoderCount hn hNL hNR
  unfold LightSourceBandHost.time
  nlinarith




















































end ThreeSum.SourceBandHostCosts

end

section


/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts

open Scales TrimScales StageBounds CostLedger BandScales






theorem time_bound (h J : ℕ) : LightSourceControls.time h J ≤ factor h J := by
  have hd := LightDownsetSize.time_bound (J*(512*h))
  unfold LightSourceControls.time LightNatPower.time Light.log2Time factor
  omega



















theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
        factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859 := by
  have hs := SourceBandHostCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hc := time_bound (microHalf (inputBits n)) (blockCount (inputBits n))
  have he : 0 < encoderCount n := hn.trans_le (SourceBandCosts.input_le_encoderCount n)
  have hm := Nat.le_mul_of_pos_right
    (factor (microHalf (inputBits n)) (blockCount (inputBits n))+500) he
  unfold LightSourceControlsHost.time
  nlinarith




























end ThreeSum.SourceControlCosts

end

section


/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts

open Scales TrimScales StageBounds CostLedger BandScales



















theorem word_mono {NL NR NL' NR' g p h J cut U D : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightSourceControlsHost.word NL NR g p h J cut U D ≤
      LightSourceControlsHost.word NL' NR' g p h J cut U D := by
  have hs := SourceBandBankLayout.word_mono (h := h) (J := J) hl hr
  unfold LightSourceControlsHost.word LightSourceBandHost.word LightSourceBandPair.word
    LightSourceBandStep.word LightSourceBandBanks.word LightSourceBandBankStep.word
  omega

theorem time_le {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ time n p U D :=
  SourceControlCosts.time_le_encoderCount hn hNL hNR

theorem space_le {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ space base n p U D :=
  SourceControlCosts.space_le_encoderCount hn hNL hNR






theorem word_le {NL NR n p U D : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.word NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ word n p U D :=
  word_mono hNL hNR

end ThreeSum.SourceFiniteCosts

end

section


/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts

open Scales TrimScales BandScales




theorem time_le {NL NR n p U M : ℕ} (hn : 0 < n) (hL : NL ≤ n) (hR : NR ≤ n) :
    LightEncodedColorSources.time NL NR (bandSize n) p (microHalf (inputBits n))
      (blockCount (inputBits n)) (mu n) U M ≤ time n p U M := by
  have h := SourceFiniteCosts.time_le (p := p) (U := U) (D := M) hn hL hR
  unfold LightEncodedColorSources.time time
  omega






end ThreeSum.EncodedColorSourcesCosts

end

section


/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources

open Light Scales TrimScales BandScales









theorem free_le_base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ base free n p M xs := by
  have h := EncodedColorWantedData.header_le_nextFree
    (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length)
    M (LightGuardedWanted.left p xs)
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hk := EncodedColorCoverData.header_end free (microHalf (inputBits n)) (blockCount (inputBits n))
  change _ ≤ base free n p M xs at h
  unfold LightGuardedWanted.wantedFree at h
  omega

variable {lim : Limits} {d : ℕ}

theorem program_meets_sourceProof {μ : ℕ → ℤ} {free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+256*mu n+17 ≤ lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ free) (hae : ae+2+2*n ≤ free)
    (hbv : bv+n ≤ free) (hbe : be+2+2*n ≤ free)
    (hcv : cv+n ≤ free) (hce : ce+2+2*n ≤ free)
    (htables : tables+ColorBandBounds.count n (bandSize n) ≤ free)
    (hrecords : rec+4*ColorBandBounds.count n (bandSize n) ≤ free)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n (bandSize n)) (bandSize n) ≤ free)
    (hspace : SourceFiniteCosts.space (base free n p M xs) n p U M ≤ lim.space)
    (hword : (SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hcover : LightCoverKeyData.Stored μ free (microHalf (inputBits n)) (blockCount (inputBits n)))
    (hwanted : LightWantedSetup.Output μ
      (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
      (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
      (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)))) :
    Meets lim LightEncodedColorSources.program 80 d (args free bv be cv ce n p xs.length) μ
      (EncodedColorSourcesCosts.time n p U M)
      (fun r ν =>
        SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
          originalA originalB originalC A B C hsA hsB hsC rA ∧
        SourceFiniteData.Stored ν (base free n p M xs) (bandSize n) p
          (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) r ∧
        LightCoverKeyData.Stored ν free (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
        LightWantedSetup.Output ν
          (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
          (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n))) ∧
        Kept μ ν (base free n p M xs)) := by
  have repB := H.2.2.1
  have repC := H.2.2.2.1
  have hnB : B.length ≤ n := repB.2.1.trans hB
  have hnC : C.length ≤ n := repC.2.1.trans hC
  have hbase := free_le_base free n p M xs
  have hdepth : d+blockCount (inputBits n)*(512*microHalf (inputBits n))+17 ≤ lim.depth := by
    rwa [BlockSourceSharing.width_eq]
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [BlockSourceSharing.width_eq]
    omega
  have hs := (SourceFiniteCosts.space_le (base := base free n p M xs) (p := p) (U := U) (D := M)
    hn hnB hnC).trans hspace
  have hw' : (LightSourceControlsHost.word B.length C.length (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (SourceFiniteCosts.word_le hnB hnC)).trans hword
  have run := LightEncodedColorSources.program_meets (μ := μ) (free := free)
    (p := p) (h := microHalf (inputBits n)) (J := blockCount (inputBits n)) (cut := mu n) (U := U) (M := M)
    (xs := xs) hw hdepth hp hcut (by omega) (by omega) (by omega) (by omega) hs hw'
    repB repC hboundB hboundC hcover hwanted
  apply run.mono (EncodedColorSourcesCosts.time_le hn hnB hnC)
  intro r ν ⟨sources,cover,wanted,kept⟩
  exact ⟨H.keep kept hA hB hC (hav.trans hbase) (hae.trans hbase) (hbv.trans hbase) (hbe.trans hbase)
    (hcv.trans hbase) (hce.trans hbase) (htables.trans hbase) (hrecords.trans hbase) (hcatalog.trans hbase),
    sources,cover,wanted,kept⟩

end ThreeSum.LightEncodedColorFiniteSources

end


theorem solution : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {free av ae bv be cv ce tables rec vals n p U M : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  {originalA originalB originalC A B C xs : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C} {rA : Int},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) (ThreeSum.Scales.mu n)))
          (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
          @LE.le.{0} Nat instLENat (@List.length.{0} Int originalA) n →
            @LE.le.{0} Nat instLENat (@List.length.{0} Int originalB) n →
              @LE.le.{0} Nat instLENat (@List.length.{0} Int originalC) n →
                @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av n) free →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                      free →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv n)
                        free →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                          free →
                        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv n)
                            free →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                              free →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) tables
                                  (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))
                                free →
                              @LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rec
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                      (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n))))
                                  free →
                                @LE.le.{0} Nat instLENat
                                    (ThreeSum.LightBandRawA.space vals
                                      (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n))
                                      (ThreeSum.BandScales.bandSize n))
                                    free →
                                  @LE.le.{0} Nat instLENat
                                      (ThreeSum.SourceFiniteCosts.space
                                        (@ThreeSum.LightEncodedColorFiniteSources.base free n p M inst xs) n p U M)
                                      lim.space →
                                    @LE.le.{0} Int Int.instLEInt
                                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceFiniteCosts.word n p U M))
                                        lim.word →
                                      (∀ (z : Int),
                                          @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
                                              originalB z →
                                            @LE.le.{0} Int Int.instLEInt
                                              (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                              (@Nat.cast.{0} Int instNatCastInt U)) →
                                        (∀ (z : Int),
                                            @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
                                                originalC z →
                                              @LE.le.{0} Int Int.instLEInt
                                                (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                                (@Nat.cast.{0} Int instNatCastInt U)) →
                                          ThreeSum.SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals
                                              (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n)
                                              originalA originalB originalC A B C hsA hsB hsC rA →
                                            ThreeSum.LightCoverKeyData.Stored μ free
                                                (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) →
                                              ThreeSum.LightWantedSetup.Output μ
                                                  (ThreeSum.LightGuardedWanted.wantedFree free
                                                    (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))
                                                    (@List.length.{0} Int xs))
                                                  M (ThreeSum.LightGuardedWanted.left p xs)
                                                  (ThreeSum.LightGuardedWanted.right
                                                    (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                    (@List.length.{0} Int xs))
                                                  (ThreeSum.LightGuardedWanted.totalKeys
                                                    (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
                                                  (@Nat.cast.{0} Int instNatCastInt
                                                    (@ThreeSum.RawAKeyLists.selected M inst
                                                      (@Nat.cast.{0} Int instNatCastInt p) xs
                                                      (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                      (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))) →
                                                Light.Meets lim ThreeSum.LightEncodedColorSources.program
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) d
                                                  (ThreeSum.LightEncodedColorFiniteSources.args free bv be cv ce n p
                                                    (@List.length.{0} Int xs))
                                                  μ (ThreeSum.EncodedColorSourcesCosts.time n p U M)
                                                  fun (r : Int) (ν : Nat → Int) =>
                                                  And
                                                    (ThreeSum.SourceFiniteData.Normalized ν av ae bv be cv ce tables rec
                                                      vals (ThreeSum.BandScales.bandSize n)
                                                      (ThreeSum.BandScales.bandSize_pos n) originalA originalB originalC
                                                      A B C hsA hsB hsC rA)
                                                    (And
                                                      (ThreeSum.SourceFiniteData.Stored ν
                                                        (@ThreeSum.LightEncodedColorFiniteSources.base free n p M inst
                                                          xs)
                                                        (ThreeSum.BandScales.bandSize n) p
                                                        (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                        (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))
                                                        (ThreeSum.Scales.mu n) B C
                                                        (@Nat.cast.{0} Int instNatCastInt
                                                          (@ThreeSum.RawAKeyLists.selected M inst
                                                            (@Nat.cast.{0} Int instNatCastInt p) xs
                                                            (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                            (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))))
                                                        r)
                                                      (And
                                                        (ThreeSum.LightCoverKeyData.Stored ν free
                                                          (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                          (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
                                                        (And
                                                          (ThreeSum.LightWantedSetup.Output ν
                                                            (ThreeSum.LightGuardedWanted.wantedFree free
                                                              (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                              (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))
                                                              (@List.length.{0} Int xs))
                                                            M (ThreeSum.LightGuardedWanted.left p xs)
                                                            (ThreeSum.LightGuardedWanted.right
                                                              (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                              (ThreeSum.Scales.blockCount
                                                                (ThreeSum.Scales.inputBits n)))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              (@List.length.{0} Int xs))
                                                            (ThreeSum.LightGuardedWanted.totalKeys
                                                              (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                                                              (ThreeSum.Scales.blockCount
                                                                (ThreeSum.Scales.inputBits n)))
                                                            (@Nat.cast.{0} Int instNatCastInt
                                                              (@ThreeSum.RawAKeyLists.selected M inst
                                                                (@Nat.cast.{0} Int instNatCastInt p) xs
                                                                (ThreeSum.Scales.microHalf
                                                                  (ThreeSum.Scales.inputBits n))
                                                                (ThreeSum.Scales.blockCount
                                                                  (ThreeSum.Scales.inputBits n)))))
                                                          (Light.Kept μ ν
                                                            (@ThreeSum.LightEncodedColorFiniteSources.base free n p M
                                                              inst xs))))) := by
  exact @ThreeSum.LightEncodedColorFiniteSources.program_meets_sourceProof

#print axioms solution
