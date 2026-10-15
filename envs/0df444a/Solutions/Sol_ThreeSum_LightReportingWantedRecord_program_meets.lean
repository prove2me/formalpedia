-- Prove2me | solution 1 for ThreeSum.LightReportingWantedRecord.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:19:14.641498+00:00
-- url     : https://prove2.me/submissions/7cea329d-0e10-4fe6-84e0-6cbb4d151150

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
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LightReportingWantedRecordCall_program_meets
import Theorems.Thm_ThreeSum_LightReportingWanted_program_meets
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_OutputDecodeRecords_global_record_block
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localRecords_getD
import Theorems.Thm_ThreeSum_Radix_representations_card_le
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum_ReportingHostWantedRecordData_cover_scalars
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_bounds


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
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
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
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedRecordData
end ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition




















































theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

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









































end ThreeSum.OneHotMask

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













































end ThreeSum.BlockCoefficientRows

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

























theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]


























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


















theorem finiteAIndices_owner {n g s : ℕ} {rs : List Record}
    (hs : s < rs.length) {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ (labelAt n g rs i.val).owner=s := by
  rw [mem_finiteAIndices,mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]

































































































end ThreeSum.BandRawA

end

section


/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators





























































@[simp] theorem rawMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (rawMasks rows).length = J := by simp [rawMasks]









end ThreeSum.BlockMaskLayout

end

section


/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule






























theorem Data.counts_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < localPrime h) :
    μ (hist0+j*localPrime h+r) = (LocalCoverMatrix.leftCount (candidate h j) h r : ℤ) ∧
    μ (hist1+j*localPrime h+r) = (LocalCoverMatrix.rightCount (candidate h j) h r : ℤ) :=
  (H j hj).2.1 r hr

























































end ThreeSum.LightLocalCoverTables

end

section


/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput

open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags













theorem of_cover {μ : ℕ → ℤ} {h allMaps matrix maps candidates histL histR : ℕ}
    (H : LightLocalCoverTables.Data μ h allMaps histL histR matrix)
    (R : LightLocalCoverTables.ScheduleRows μ h maps)
    (I : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)) :
    Input μ h maps candidates histL histR := by
  refine ⟨I,?_,?_,?_,?_⟩
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).1
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).2
  · intro k hk r hr
    exact (H.counts_read hk hr).1
  · intro k hk r hr
    exact (H.counts_read hk hr).2

































end ThreeSum.BlockSourceCoverInput

end

section


/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000









theorem localCount_pos (h : ℕ) : 0 < localCount h := Nat.mul_pos (schedule_pos h) (layerCount_pos h)

































theorem localIndex_lt {h J k j : ℕ} (hj : j < J) : localIndex h J k j < localCount h :=
  indices_getD_lt (localCount_pos h) hj










































theorem original_occurrence_index {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    (((globalRecords h J).getD k (outputDefault h J)) j).1.val = occurrenceIndex h J k j.val := by
  rw [global_record_block hk j,localRecords_getD (localIndex_lt j.isLt)]
  rfl




















end ThreeSum.OutputDecodeRecords

end

section


/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode

open OutputDecodeOrder OutputDecodeRecords GlobalEncoding

set_option maxHeartbeats 1500000





theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [code,pow_succ']
    omega











theorem code_indices {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) :
    indices T J (code T M J k) = (indices (T*M) J k).map (fun i => i/M) := by
  induction J generalizing k with
  | zero => rfl
  | succ J ih =>
    have hd := last_lt hT hM k
    have hdiv : code T M (J+1) k/T = code T M J (k/(T*M)) := by
      rw [code,Nat.mul_comm T (code T M J (k/(T*M))),
        Nat.add_mul_div_right _ _ hT,Nat.div_eq_of_lt hd,Nat.zero_add]
    have hmod : code T M (J+1) k%T = (k%(T*M))/M := by
      have hm := Nat.div_add_mod (code T M (J+1) k) T
      rw [hdiv] at hm
      have he : code T M (J+1) k = (k%(T*M))/M+T*code T M J (k/(T*M)) := rfl
      omega
    rw [indices,hdiv,hmod,ih]
    simp only [indices,List.map_append,List.map_cons,List.map_nil]

theorem source_code_lt (h J k : ℕ) :
    code (scheduleSize h) (layerCount h) J k < scheduleSize h^J :=
  code_lt (schedule_pos h) (layerCount_pos h) J k

theorem source_code_coordinate (h J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j 0 =
      occurrenceIndex h J k j := by
  rw [code_indices (schedule_pos h) (layerCount_pos h)]
  have hi : j < (indices (scheduleSize h*layerCount h) J k).length := by
    rw [indices_length]
    exact hj
  rw [List.getD_map_of_lt _ hi 0 0]
  rfl

end ThreeSum.OutputDecodeOccurrenceCode

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

theorem leftSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by
  unfold leftSource
  rw [he]

theorem rightSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    rightSource P d B b q = rightSource P d B b q' := by
  unfold rightSource
  rw [he]

theorem stored_left_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (leftSource P B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (leftSource P B b q') (J*(512*h)) := by
  rw [← leftSource_eq_of_occurrences P B b he]
  exact hs

theorem stored_right_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P d : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (rightSource P d B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (rightSource P d B b q') (J*(512*h)) := by
  rw [← rightSource_eq_of_occurrences P d B b he]
  exact hs













































































end ThreeSum.BlockSourceSharing

end

section


/-!
# Exact source-bank order and reuse by decoded global outputs

A source-bank row is the big-endian radix expansion of its physical index.
Its representative carries a fixed legal output subset solely to reuse the
original source definitions. No output-subset choice enters the stored row
or the source function. The actual global-output decoder supplies exactly
the bank index needed by a query.
-/

namespace ThreeSum.BlockSourceOccurrenceOrder

open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration










theorem row_coordinate {h J k j : ℕ} (hj : j < J) :
    occurrenceIndices (outputOccurrences (representative h J k)) j =
      (indices (scheduleSize h) J k).getD j 0 := by
  rw [occurrenceIndices_fin _ ⟨j,hj⟩]
  rfl

theorem decoded_occurrences {h J k : ℕ} (hk : k < localCount h^J) :
    outputOccurrences (representative h J (code (scheduleSize h) (layerCount h) J k)) =
      outputOccurrences ((globalRecords h J).getD k (outputDefault h J)) := by
  funext j
  apply Fin.ext
  change (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j.val 0 = _
  rw [source_code_coordinate h J k j.isLt]
  exact (original_occurrence_index hk j).symm















end ThreeSum.BlockSourceOccurrenceOrder

end

section


/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000






























theorem BankAt.reuse {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i : ℕ} {μ : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q q' : GlobalOutput h J}
    (H : BankAt μ base count cut i P shift B b A a q)
    (ho : outputOccurrences q = outputOccurrences q') :
    BankAt μ base count cut i P shift B b A a q' :=
  ⟨BlockSourceSharing.stored_left_reuse P B b ho H.left,
    BlockSourceSharing.stored_right_reuse P shift A a ho H.right,H.headerLeft,H.headerRight⟩

























variable {lim : Limits} {P : Program} {d : ℕ}


































































































end ThreeSum.LightBlockSourceBatch

end

section


/-!
# Constructed occurrence rows and their shared source banks

The first call constructs every big-endian occurrence row from its physical
bank index. The second call builds the two retained original source-stage
families once for that row. Original-band histograms and selected cover data
remain available throughout. No array of complete output records is read.
-/

namespace ThreeSum.LightBlockSourceCatalog

open Light BlockEncoding GlobalEncoding BlockIndex BlockCoefficientRows
open SubsetAddress LocalCoverBounds BlockSourceEncoding LightBlockSourceBatchLayout
open BlockSourceOccurrenceOrder OutputDecodeOrder OutputDecodeRecords

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000





































theorem Stored.decoded {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {μ : ℕ → ℤ} {h J base cut k : ℕ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ}
    (H : Stored μ h J base cut P shift B b A a) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ base (count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      P shift B b A a ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H _ (OutputDecodeOccurrenceCode.source_code_lt h J k)).reuse (decoded_occurrences hk)

variable {lim : Limits} {P : Program} {d : ℕ}

















































































end ThreeSum.LightBlockSourceCatalog

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



























































theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _



















theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]



























































































































































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

theorem mem_owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    w.1∈finiteAIndices n g rs (owner rs w) :=
  (finiteAIndices_owner (owner_lt rs w)).mpr rfl


























































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


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets












theorem len_le_cap (n g i : ℕ) : len n g i ≤ cap n g := by
  have hn := stop_le n g i
  have hg := length_le n g i
  unfold len cap
  exact le_min (by omega) hg

theorem input_index {n g i j : ℕ} (hg : 0 < g) (hi : i < size n g) (hj : j < len n g i) :
    start g i+j < n := by
  have hlo := start_lt_stop hg hi
  have hhi := stop_le n g i
  unfold len at hj
  omega



























































































end ThreeSum.SourceBandLayout

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder












































































theorem At.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i k : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (hk : k < OutputDecodeRecords.localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (OutputDecodeRecords.layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (OutputDecodeRecords.outputDefault h J)) :=
  LightBlockSourceCatalog.Stored.decoded H hk

end ThreeSum.SourceBandBankLayout

end

section


/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData

open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords
















theorem Stored.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt (first base) h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H.banks i hi).decoded hk































end ThreeSum.SourceBandBankData

end

section


/-! # The shared source banks in the physical finite reporting domains -/

namespace ThreeSum.SourceBandFinite

open GlobalEncoding OutputDecodeRecords

theorem source_eq_finiteBandPositions (n g i : ℕ) :
    SourceBandPartition.source n g i=BandRawA.finiteBandPositions n g i := by
  ext t
  rw [SourceBandPartition.mem_source,BandRawA.mem_finiteBandPositions,BandRawA.mem_bandPositions]













theorem decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (SourceBandBankLayout.baseAt (base+5) h J cut i)
      (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) p shift
      (BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by
  simpa only [SourceBandBankData.first,source_eq_finiteBandPositions] using H.decoded hi hk

end ThreeSum.SourceBandFinite

end

section


/-!
# Selected controls from the actual retained original-source catalogs

The selector's concrete header reads follow from the existing band,
occurrence-bank and local-cover constructors. Its two independently chosen
bands supply the unchanged physical buckets and the exact original-output
source stages. No output-subset loop or source reconstruction is involved.
-/

namespace ThreeSum.ReportingHostSourceSelectionStored

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection OutputDecodeRecords BlockCoefficientRows

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000











































































theorem sources_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J occ i j output : ℕ} {shift : ℤ}
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g)
    (hk : output<localCount h^J) :
    let code := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    let X := retained pair bank cover NL NR g h J (LightBlockQuery.sourceCut h J) occ i j code
    ReportingHostLevelData.Sources μ (p : ℤ) shift
      (BandRawA.finiteBandPositions NL g i) (BandRawA.finiteBandPositions NR g j)
      (fun t : Fin NL => fB t.val) (fun t : Fin NR => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) X.stagesL X.stagesR := by
  have hLi : i<SourceBandPairSlices.count NL NR g := hi.trans_le (le_max_left _ _)
  have hRj : j<SourceBandPairSlices.count NL NR g := hj.trans_le (le_max_right _ _)
  exact ⟨(SourceBandFinite.decoded HB hLi hk).left,(SourceBandFinite.decoded HB hRj hk).right⟩

theorem occurrence_rows_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J cut occ i j output : ℕ} {shift : ℤ}
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (hk : output<localCount h^J) (t : ℕ) (ht : t<J) :
    let code := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    let X := retained pair bank cover NL NR g h J cut occ i j code
    μ (occurrenceRow X code J+t)=
      (occurrenceIndices (BlockEncoding.outputOccurrences
        ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J))) t : ℤ) := by
  have H := HB.rows _ (OutputDecodeOccurrenceCode.source_code_lt h J output) t ht
  rw [← BlockSourceOccurrenceOrder.row_coordinate ht,
    BlockSourceOccurrenceOrder.decoded_occurrences hk] at H
  exact H





































end ThreeSum.ReportingHostSourceSelectionStored

end

section


/-! # Exact retained cells of one shared reporting catalog -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000































































theorem Tables.reporting {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalEncoding.GlobalOutput h J)
    (H : Tables μ D hk (BlockIndexedQuery.leftSource p B b q)
      (BlockIndexedQuery.rightSource p shift C c q)) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c q :=
  ⟨H.index,H.pointers,H.boxes⟩

end ThreeSum.SharedReportingBankData

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


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000







































































theorem baseAt_mono (base h J : ℕ) : Monotone (baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (levelOffset_mono h J (boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) :=
  finish_level base h J k (boxCut h J)










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























end ThreeSum.SharedReportingBankLevels

end

section


/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources

open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords












































theorem tables_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q=outputOccurrences q')
    (H : Tables μ D hk (leftSource p B b q) (rightSource p shift C c q)) :
    Tables μ D hk (leftSource p B b q') (rightSource p shift C c q') := by
  rw [← BlockSourceSharing.leftSource_eq_of_occurrences p B b ho,
    ← BlockSourceSharing.rightSource_eq_of_occurrences p shift C c ho]
  exact H










theorem reporting_decoded {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k output record : ℕ} {μ : ℕ → ℤ}
    {D : ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (houtput : output < localCount h^J)
    (H : Entry μ record D hk
      (leftSource p B b (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))
      (rightSource p shift C c (representative h J
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)))) :
    ReportingHostLevelData.Stored μ D hk p shift B C b c
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) :=
  (tables_reuse p shift B C b c (decoded_occurrences houtput) H.tables).reporting p shift B C b c _

end ThreeSum.SharedReportingBankSources

end

section


/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000






















theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    rank nb nc s i j < pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)































theorem rowBase_next (base h J K q : ℕ) :
    baseAt (rowBase base h J K q) h J K=rowBase base h J K (q+1) := by
  unfold rowBase baseAt
  ring
theorem rowBase_mono (base h J K : ℕ) : Monotone (rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _













































































end ThreeSum.SharedReportingBankRows

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






























































theorem Stored.row {μ : ℕ → ℤ} {free h J NB NC g s i j : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    Built μ (rowRecord (records free) (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase (payload free h J NB NC g) h J (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      h J (levels J)
      (BlockIndexedQuery.leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (BlockIndexedQuery.rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) :=
  H.rows s hs i hi j hj (rank_lt hs hi hj)

end ThreeSum.SharedReportingBankHeader

end

section


/-! # Constant-time row addresses and original-output reporting interfaces -/

namespace ThreeSum.SharedReportingBankAccess

open Light GlobalEncoding BlockIndexedQuery OutputDecodeRecords
open SharedReportingBankRows SharedReportingBankHeader SharedReportingBankLevels
open SharedReportingBankData SharedReportingBankSources

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000




























theorem record_end {free h J NB NC g s i j : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    recordAt free J NB NC g s i j+5*levels J ≤ payload free h J NB NC g := by
  have hr := rank_lt hs hi hj
  have hh := Nat.mul_le_mul_left (5*levels J) (show
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by exact hr)
  unfold recordAt slot rowRecord payload
  nlinarith

theorem row_end {free h J NB NC g s i j : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    baseAt (payloadAt free h J NB NC g s i j) h J (levels J) ≤
      SharedReportingBankHeader.finish free h J NB NC g := by
  unfold payloadAt
  rw [rowBase_next]
  exact rowBase_mono _ h J (levels J) (rank_lt hs hi hj)

theorem level_end {free h J NB NC g s i j k : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) :
    (levelCatalog free h J NB NC g s i j k).indexBase+LightReportingPrefixCatalog.count h k ≤
      SharedReportingBankHeader.finish free h J NB NC g ∧
    (levelCatalog free h J NB NC g s i j k).ptrBase+LightReportingPrefixCatalog.count h k ≤
      SharedReportingBankHeader.finish free h J NB NC g ∧
    (levelCatalog free h J NB NC g s i j k).boxBase+LightReportingPrefixCatalog.count h k*
      LightReportingSuffixCatalog.stride ((J-k)*(512*h)) (levelCatalog free h J NB NC g s i j k).boxCut ≤
      SharedReportingBankHeader.finish free h J NB NC g := by
  have hend := catalog_end (payloadAt free h J NB NC g s i j) h J k
  have hbefore := (baseAt_mono (payloadAt free h J NB NC g s i j) h J
    (show k+1 ≤ levels J from hk)).trans (row_end hs hi hj)
  exact ⟨hend.1.trans hbefore,hend.2.1.trans hbefore,hend.2.2.trans hbefore⟩

theorem entry {μ : ℕ → ℤ} {free h J NB NC g s i j k : ℕ} {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) (hkJ : k ≤ J) :
    Entry μ (recordAt free J NB NC g s i j+5*k) (levelCatalog free h J NB NC g s i j k) hkJ
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) := by
  obtain ⟨hk',Hk⟩ := H.row hs hi hj k hk
  exact Hk

theorem bounds {source free h J NB NC g s i j k stop : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J)
    (hsource : SourceBandBankData.finish source NB NC g h J (2*h*J) ≤ free)
    (hstop : SharedReportingBankHeader.finish free h J NB NC g ≤ stop) :
    ReportingHostLevelData.Bounds h J k (levelCatalog free h J NB NC g s i j k)
      (leftBase source h J (2*h*J) i s) (rightBase source h J (2*h*J) j s) stop := by
  have hl := source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hi.trans_le (le_max_left _ _)) hs
  have hr := source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hj.trans_le (le_max_right _ _)) hs
  have hf : free ≤ stop := (Nat.le_add_right free 9).trans
    ((records_le_payload free h J NB NC g).trans ((payload_le_finish free h J NB NC g).trans hstop))
  have he := level_end (free := free) hs hi hj hk
  exact ⟨hl.2.2.1.trans (hsource.trans hf),hr.2.2.2.trans (hsource.trans hf),
    he.1.trans hstop,he.2.1.trans hstop,he.2.2.trans hstop⟩

theorem original {μ : ℕ → ℤ} {free h J NB NC g output i j k : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (houtput : output < localCount h^J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) (hkJ : k ≤ J) :
    let s := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    SegN μ (recordAt free J NB NC g s i j+5*k) ((levelCatalog free h J NB NC g s i j k).record h k) ∧
    ReportingHostLevelData.Stored μ (levelCatalog free h J NB NC g s i j k) hkJ p shift
      (BandRawA.finiteBandPositions NB g i) (BandRawA.finiteBandPositions NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD output (OutputDecodeRecords.outputDefault h J)) := by
  have hs : OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output <
      LightBlockSourceCatalog.count h J := OutputDecodeOccurrenceCode.source_code_lt h J output
  have Hk := entry H hs hi hj hk hkJ
  refine ⟨Hk.header,?_⟩
  simpa only [SourceBandFinite.source_eq_finiteBandPositions] using
    reporting_decoded p shift (SourceBandPartition.source NB g i) (SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val) houtput Hk

end ThreeSum.SharedReportingBankAccess

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



































































theorem make_bounds {root K W G T cap cap' : ℕ} (hc : cap≤cap') :
    Bounds (make root K W G T cap') root K W G T cap := by
  have hf : slot root cap (K+1)≤slot root cap' (K+1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨rfl,hf,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_,?_,le_rfl,le_rfl,le_rfl,?_,le_rfl,le_rfl⟩
  · simp only [make]
    omega
  · simp only [make]
    omega
  · rfl

theorem terminal_count_le (h J k : ℕ) : LightReportingTerminalMasks.count h J k≤2^(width h J) := by
  have hh : (J-k)*(2*h)≤width h J := by
    exact (Nat.mul_le_mul_left _ (by omega : 2*h≤512*h)).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le J k))
  exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) hh)

theorem terminal_stop_mono {base W n T : ℕ} (hn : n≤T) :
    LightReportingTerminalPreparation.stop base W n≤LightReportingTerminalPreparation.stop base W T := by
  unfold LightReportingTerminalPreparation.stop LightReportingTerminalPreparation.span
  omega

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

theorem root_mass_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    rootMass (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      massBound N NB NC (representationCap h J) := by
  rw [rootMass_eq]
  have hp : (A ×ˢ (B ×ˢ C)).card≤N*NB*NC := by
    rw [Finset.card_product,Finset.card_product]
    calc
      _ ≤ N*(NB*NC) := Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
      _ = _ := by ring
  exact (Finset.card_filter_le _ _).trans
    ((raw_card_le (A ×ˢ (B ×ˢ C)) a b c hP hg).trans
      (Nat.mul_le_mul_right _ hp))

theorem capacity_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    capacity (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      capacityBound N NB NC (representationCap h J) (groupSize h) :=
  Nat.mul_le_mul_right _ (Nat.add_le_add_right (root_mass_le A B C a b c w hP hg hA hB hC) 1)

end Mass

end ThreeSum.ReportingHostWantedLayout

end

section


/-! # Typed contents of the executed wanted access and scratch records -/

namespace ThreeSum.ReportingHostWantedControls

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout

























































theorem rawRows_end (layoutHeader J : ℕ) : rawRows layoutHeader J+J=access layoutHeader J := by
  rfl

theorem rawRows_before_packed (layoutHeader J : ℕ) : rawRows layoutHeader J+J≤packed layoutHeader J := by
  rw [rawRows_end]
  exact Nat.le_add_right _ _



end ThreeSum.ReportingHostWantedControls

end

section


/-!
# Original-domain facts carried by the two actual wanted records

All source stages, buckets, occurrence rows, and per-level catalogs below
come from the retained concrete constructors. The decoder supplies the
unaltered original Q masks used by the guarded reporter.
-/

namespace ThreeSum.ReportingHostWantedRecordData

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostSourceSelectionStored OutputDecodeRecords

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false












theorem selected_value (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List Record) (w : Wanted h J (AType n g rs)) (output : ℕ) :
    (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output).av=
      valueAt n g rs fA w.1.val := by
  change fA (BandRawA.labelAt n g rs w.1.val).position=(values fA (items n g rs)).getD w.1.val 0
  exact (values_getD fA w.1.isLt).symm















section Stored

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
  {n NB NC g pair bank cover h J p occ srcB srcC report output : ℕ}
  {rs : List Record} {shift : ℤ} (w : Wanted h J (AType n g rs))

theorem sources
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    ReportingHostLevelData.Sources μ (p : ℤ) shift
      (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
      (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
      (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 S.baseL S.baseR := by
  rw [he]
  exact sources_decoded (pair := pair) (cover := cover) HB hi hj houtput

theorem catalog
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    {k : ℕ} (hk : k<SharedReportingBankHeader.levels J) (hkJ : k≤J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := catalogs n NB NC g report h J rs w output k
    SegN μ (S.catalog+5*k) (D.record h k) ∧
      ReportingHostLevelData.Stored μ D hkJ (p : ℤ) shift
        (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
        (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
        (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 := by
  rw [he]
  exact SharedReportingBankAccess.original HQ houtput hi hj hk hkJ

theorem buckets
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (BlockSourceEncoding.modulus h J) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    SourceBuckets.Stored μ (fun i => LightSourceResidues.key p (BlockSourceEncoding.modulus h J) 0 (left rs fB w i))
      S.NL (BlockSourceEncoding.modulus h J) S.offsetsL S.flatL ∧
    SourceBuckets.Stored μ (fun i => LightSourceResidues.key p (BlockSourceEncoding.modulus h J) shift (right rs fC w i))
      S.NR (BlockSourceEncoding.modulus h J) S.offsetsR S.flatR :=
  ⟨(HP.left _ hi).buckets,(HP.right _ hj).buckets⟩

theorem occurrences
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    {t : ℕ} (ht : t<J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    μ (S.occ+t)=(occurrenceIndices (outputOccurrences w.2.2) t : ℤ) := by
  rw [he]
  exact occurrence_rows_decoded HB houtput t ht

theorem cover_input (HC : LightCoverKeyData.Stored μ cover h J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    BlockSourceCoverInput.Input μ h S.maps S.candidates S.histL S.histR :=
  BlockSourceCoverInput.of_cover HC.data HC.rows HC.indices

theorem source_reads (hg : 0<g)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (hreadB : ∀ i<NB, μ (srcB+i)=fB i) (hreadC : ∀ i<NC, μ (srcC+i)=fC i) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    (∀ i<S.NL, μ (S.srcL+i)=left rs fB w i) ∧
      (∀ i<S.NR, μ (S.srcR+i)=right rs fC w i) := by
  constructor
  · intro i hi'
    have hh := hreadB _ (SourceBandLayout.input_index hg hi hi')
    simpa only [selected,ofAccess,LightReportingWantedAccess.selection,retained,
      ReportingHostWantedOriginal.left,Nat.add_assoc] using hh
  · intro i hi'
    have hh := hreadC _ (SourceBandLayout.input_index hg hj hi')
    simpa only [selected,ofAccess,LightReportingWantedAccess.selection,retained,
      ReportingHostWantedOriginal.right,Nat.add_assoc] using hh

theorem raw_rows {dst N i : ℕ}
    (HD : LightWantedDecode.Stored μ (decoded dst) N h J i output)
    (he : w.2.2=LightOutputDecodeOriginal.output h J output) :
    SegN μ (rawRows dst J) (rawMasks (outputRows w.2.2)) := by
  intro t ht
  have ht' : t<J := by simpa only [List.length_map,rawMasks_length] using ht
  have hh := HD.rows.masks ⟨t,ht'⟩
  simpa only [he,rawRows,rawMasks,outputRows,List.getElem_map,List.getElem_ofFn] using hh

end Stored


















end ThreeSum.ReportingHostWantedRecordData

end

section


/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostWantedLayout ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false




































































































section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem wanted_frontier_length_le {h J K N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    (ReportingHostFrontier.frontier (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length≤
      massBound N NB NC (representationCap h J) := by
  have hh := ReportingHostFrontier.frontier_length_le_domain
    (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w hK
  rw [← rootMass_eq] at hh
  exact hh.trans (root_mass_le A B C a b c w hP hg hA hB hC)

theorem wanted_depth {lim : Limits} {h J K N NB NC d : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC)
    (hd : d+wantedDepth h J K N NB NC≤lim.depth) :
    d+K+2*LightBlockQuery.width h J+
      (ReportingHostFrontier.frontier (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length+
      LightReportingTerminalMasks.count h J K+30≤lim.depth := by
  have hf := wanted_frontier_length_le (shift := shift) A B C a b c w hK hP hg hA hB hC
  have ht := terminal_count_le h J K
  unfold wantedDepth at hd
  omega















end Raw
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000































































































































theorem wanted_catalog_bounds {pair bank cover report NB NC g h J occ i j code stop K : ℕ}
    (hi : i<BandPartition.size NB g) (hj : j<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J) (hK : K≤LightSwitchDepth.depth J)
    (hbank : SourceBandBankData.finish bank NB NC g h J (LightBlockQuery.sourceCut h J)≤report)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤stop) :
    SharedReportingBankAccess.recordAt report J NB NC g code i j+5*(K+1)≤stop ∧
    ∀ k≤K, ReportingHostLevelData.Bounds h J k
      (SharedReportingBankAccess.levelCatalog report h J NB NC g code i j k)
      (retained pair bank cover NB NC g h J (LightBlockQuery.sourceCut h J) occ i j code).stagesL
      (retained pair bank cover NB NC g h J (LightBlockQuery.sourceCut h J) occ i j code).stagesR stop := by
  have he := (SharedReportingBankAccess.record_end (free := report) hk hi hj).trans
    ((SharedReportingBankHeader.payload_le_finish report h J NB NC g).trans hreport)
  refine ⟨?_,?_⟩
  · unfold SharedReportingBankHeader.levels at he
    omega
  · intro k hkk
    exact SharedReportingBankAccess.bounds hk hi hj (by unfold SharedReportingBankHeader.levels; omega) hbank hreport

end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# The actual record loader decides its selected original owner fiber

All reporting semantics below are derived from the retained source/cover/
catalog constructors and the actual decoder. The scratch geometry is the
executed layout; the capacity follows from the original physical counts.
-/

namespace ThreeSum.LightReportingWantedRecord

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostFrontierLayout ReportingHostSourceSelectionStored OutputDecodeRecords
open ReportingHostWantedRecordData SharedReportingBankResourceBounds

set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n NB NC g pair bank cover h J p occ srcB srcC report output dst counter K old threshold V d i : ℕ}
    {rs : List Record} {shift : ℤ}
    (w : Wanted h J (AType n g rs))
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (BlockSourceEncoding.modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    (hg : 0<g) (hp : 0<p) (hguard : 4*(p : ℤ)≤globalModulus h J)
    (hK : K≤LightSwitchDepth.depth J) (hKJ : K≤J)
    (hkey : globalModulus h J∣valueAt n g rs fA w.1.val%(p : ℤ)+
      lift w.2.1*(p : ℤ)+shift-globalKey w.2.2)
    (hselected : Seg μ (access dst J)
      (record (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output)))
    (hlayout : SegN μ dst (values (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC)))
    (hdecoded : LightWantedDecode.Stored μ (decoded dst) (items n g rs).length h J i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hends : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs w.1.val pair bank cover NB NC h J
        (LightBlockQuery.sourceCut h J) occ (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output))
      pair bank cover srcB srcC (ownerRecord n g rs w.1.val).b (ownerRecord n g rs w.1.val).c
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output) h J
      (LightBlockQuery.sourceCut h J) counter)
    (hbank : SourceBandBankData.finish bank NB NC g h J (LightBlockQuery.sourceCut h J)≤report)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤counter)
    (hbuffers : WantedBuffers lim dst h J K (items n g rs).length NB NC V)
    (hqueries : ∀ k≤K, ReportingHostLevelData.Scratch lim h J k
      (catalogs n NB NC g report h J rs w output k)
      (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b).card
      (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c).card
      (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC).maskBase
      (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC).work)
    (hw : (lim.space : ℤ)≤lim.word)
    (hrecordSpace : LightReportingWantedRecordCall.space (access dst J) dst cover counter h J K≤lim.space)
    (hselectedWords : ∀ z∈record (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output), |z|≤lim.word)
    (hguardWord : ((old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤lim.word) (hvaluesC : ∀ j<NC, |fC j|≤lim.word)
    (htarget : ∀ j<NB, |valueAt n g rs fA w.1.val+fB j|≤lim.word)
    (hcountWord : ((NB*NC : ℕ) : ℤ)≤lim.word)
    (hd : d+wantedDepth h J K (items n g rs).length NB NC≤lim.depth) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := catalogs n NB NC g report h J rs w output
    Meets lim LightReportingWantedRecordCall.program 138 d
      [access dst J,dst,h,J,K,BlockSourceEncoding.modulus h J,cover,counter] μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w)
        S.NL S.NR old threshold (localItems h J n NB NC g p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w ∨
          Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        KeptBut μ ν (packed dst J) counter 1) := by
  let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  let D := catalogs n NB NC g report h J rs w output
  let L := LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC
  let A := finiteAIndices n g rs (owner rs w)
  let B := finiteBandPositions NB g (ownerRecord n g rs w.1.val).b
  let C := finiteBandPositions NC g (ownerRecord n g rs w.1.val).c
  let a := fun i : AType n g rs => valueAt n g rs fA i.val
  let b := fun i : Fin NB => fB i.val
  let c := fun i : Fin NC => fC i.val
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hI : I=localItems h J n NB NC g p rs fA fB fC shift w := rfl
  have haCard : A.card≤(items n g rs).length := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ A)
  have hbCard : B.card≤NB := by simpa only [Fintype.card_fin] using (Finset.card_le_univ B)
  have hcCard : C.card≤NC := by simpa only [Fintype.card_fin] using (Finset.card_le_univ C)
  have hcapacity := capacity_le (shift := shift) A B C a b c w
    (by exact_mod_cast hp) hguard haCard hbCard hcCard
  have hgeo := make_bounds (root := ReportingHostWantedLayout.root dst J)
    (K := K) (W := LightBlockQuery.width h J) (G := groupSize h)
    (T := 2^(LightBlockQuery.width h J)) hcapacity
  change Bounds L (ReportingHostWantedLayout.root dst J) K (LightBlockQuery.width h J)
    (groupSize h) (2^(LightBlockQuery.width h J)) (capacity I w) at hgeo
  have hterminal := terminal_count_le h J K
  have hdepth := wanted_depth (shift := shift) A B C a b c w hKJ (by exact_mod_cast hp) hguard haCard hbCard hcCard hd
  have hd' : d<lim.depth := by
    unfold wantedDepth at hd
    omega
  have hsource := sources (fA := fA) (pair := pair) (cover := cover) (srcB := srcB) (srcC := srcC)
    (report := report) w HB hi hj houtput he
  have hcatalog (k : ℕ) (hk : k≤K) := catalog (fA := fA) (pair := pair) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) w HQ hi hj houtput he
    (show k<SharedReportingBankHeader.levels J by unfold SharedReportingBankHeader.levels; omega) (hk.trans hKJ)
  have hcatBounds := wanted_catalog_bounds (pair := pair) (cover := cover) (occ := occ)
    hi hj (OutputDecodeOccurrenceCode.source_code_lt h J output) hK hbank hreport
  have hmeta : ∀ k≤K, SegN μ (S.catalog+5*k) ((D k).record h k) := fun k hk => (hcatalog k hk).1
  have hcatStored : ∀ (k : ℕ) (hk : k≤K),
      ReportingHostLevelData.Stored μ (D k) (hk.trans hKJ) (p : ℤ) shift B C b c w.2.2 :=
    fun k hk => (hcatalog k hk).2
  have hcatBounds' : ∀ k≤K, ReportingHostLevelData.Bounds h J k (D k) S.baseL S.baseR counter := hcatBounds.2
  have hmetaEnd : S.catalog+5*(K+1)≤counter := hcatBounds.1
  have hraw := raw_rows (w := w) hdecoded he
  have hscalars := cover_scalars HC
  have hbuckets := ReportingHostWantedRecordData.buckets (fA := fA) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) (report := report) (output := output) w HP hi hj
  have hcoverInput := ReportingHostWantedRecordData.cover_input (fA := fA) (NB := NB) (NC := NC)
    (pair := pair) (bank := bank) (occ := occ) (srcB := srcB) (srcC := srcC)
    (report := report) (output := output) w HC
  have hreads := source_reads (pair := pair) (bank := bank) (cover := cover) (h := h) (J := J)
    (occ := occ) (report := report) (output := output) (fA := fA) w hg hi hj hreadB hreadC
  have hv : S.av=a w.1 := selected_value fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  have hcounts : S.NL=leftCount rs NB w ∧ S.NR=rightCount rs NC w := ⟨rfl,rfl⟩
  have ha : |a w.1|≤lim.word := by
    rw [← hv]
    exact hselectedWords S.av (by simp only [record,List.mem_cons]; exact Or.inl rfl)
  have hlocalB (j : ℕ) (hj' : j<S.NL) : BandPartition.start g (ownerRecord n g rs w.1.val).b+j<NB :=
    SourceBandLayout.input_index hg hi hj'
  have hlocalC (j : ℕ) (hj' : j<S.NR) : BandPartition.start g (ownerRecord n g rs w.1.val).c+j<NC :=
    SourceBandLayout.input_index hg hj hj'
  have hcountL : S.NL≤NB := (SourceBandLayout.len_le_cap NB g _).trans (min_le_left _ _)
  have hcountR : S.NR≤NC := (SourceBandLayout.len_le_cap NC g _).trans (min_le_left _ _)
  have hcountLocal : ((S.NL*S.NR : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul hcountL hcountR)).trans hcountWord
  have hoccEnd : S.occ+J≤counter := hends.occurrence
  have hreportRun := LightReportingWanted.program_meets (μ := μ) (d := d+1)
    (srcL := S.srcL) (srcR := S.srcR) (offsetsL := S.offsetsL) (offsetsR := S.offsetsR)
    (flatL := S.flatL) (flatR := S.flatR) (NL := S.NL) (NR := S.NR) (occ := S.occ)
    (maps := S.maps) (candidates := S.candidates) (histL := S.histL) (histR := S.histR)
    (root := L.root) (catalogs := S.catalog) (rawRows := rawRows dst J) (rows := packed dst J)
    (cover := cover) (counter := counter) (baseL := S.baseL) (baseR := S.baseR)
    (masks := L.masks) (childL := L.childL) (childR := L.childR) (counts := L.counts)
    (selected := L.selected) (maskBase := L.maskBase) (work := L.work)
    (terminalMasks := L.terminalMasks) (masksL := L.masksL) (masksR := L.masksR)
    (base := L.base) (bitBase := L.bitBase) (rowOut := L.rowOut)
    p shift (left rs fB w) (right rs fC w) A B C a b c w D hKJ
    ⟨mem_owner rs w,hkey⟩ hw hsource hcatStored hcatBounds' hqueries hmeta hmetaEnd
    (rawRows_before_packed dst J) (by change packed dst J+J≤ReportingHostWantedLayout.root dst J; rfl)
    (by unfold rawRows decoded; omega) hscalars.1 (by have hh := hends.coverHeader; omega)
    hraw hcounterRead hthreshold hguardWord
    hgeo.frontier hgeo.masks hgeo.childL hgeo.childR hgeo.counts hgeo.selected
    hbuffers.parameters hbuffers.pack hbuckets.1 hbuckets.2
    hends.sourceL hends.sourceR hends.offsetsL hends.offsetsR hends.flatL hends.flatR
    (by unfold packed access decoded; omega)
    (Or.inr hends.occurrence) hends.maps hends.candidates hends.histL hends.histR
    hgeo.terminalFrontier
    ((Nat.add_le_add_left hterminal _).trans hgeo.terminalMasks)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksL)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksR)
    ((terminal_stop_mono hterminal).trans hgeo.stop) hgeo.bits hgeo.rowOut
    hbuffers.terminal hword (fun j hj' => occurrences (fA := fA) (pair := pair) (cover := cover)
      (srcB := srcB) (srcC := srcC) (report := report) w HB houtput he hj')
    hcoverInput hreads.1 hreads.2 (fun j hj' => hvaluesB _ (hlocalB j hj'))
    (fun j hj' => hvaluesC _ (hlocalC j hj')) ha (fun j hj' => htarget _ (hlocalB j hj'))
    hcountLocal (by omega)
  have hreportCall : Meets lim LightReportingWanted.program 137 (d+1)
      (arguments S L dst cover counter h J K) μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w)
        S.NL S.NR old threshold I w D K)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass I w ∨
          Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass I w : ℕ) : ℤ) ∧ KeptBut μ ν (packed dst J) counter 1) := by
    simpa only [arguments,hv,Terminal,← hI,← hcounts.1,← hcounts.2,a] using hreportRun
  exact LightReportingWantedRecordCall.program_meets hselected hlayout hscalars.2.1 hscalars.2.2
    hw hd' hrecordSpace hselectedWords hbuffers.values hreportCall

end ThreeSum.LightReportingWantedRecord

end


theorem solution : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n NB NC g pair bank cover h J p occ srcB srcC report output dst counter K old threshold V d i : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (w : ThreeSum.RawReporting.Wanted.{0} h J (ThreeSum.ReportingHostWantedOriginal.AType n g rs))
  (HP : ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (ThreeSum.BlockSourceEncoding.modulus h J) shift)
  (HB :
    ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J (ThreeSum.LightBlockQuery.sourceCut h J) occ
      (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC : ThreeSum.LightCoverKeyData.Stored μ cover h J)
  (HQ : ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).b
      (ThreeSum.BandPartition.size NB g))
  (hj :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).c
      (ThreeSum.BandPartition.size NC g))
  (houtput :
    @LT.lt.{0} Nat instLTNat output
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount h) J))
  (he :
    @Eq.{1} (ThreeSum.GlobalEncoding.GlobalOutput h J)
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (ThreeSum.LightOutputDecodeOriginal.output h J output))
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt p))
      (ThreeSum.GlobalEncoding.globalModulus h J))
  (hK : @LE.le.{0} Nat instLENat K (ThreeSum.LightSwitchDepth.depth J)) (hKJ : @LE.le.{0} Nat instLENat K J)
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt n g rs fA
                (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J)
                  (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p)))
          shift)
        (@ThreeSum.GlobalEncoding.globalKey h J
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w)))))
  (hselected :
    Light.Seg μ (ThreeSum.ReportingHostWantedLayout.access dst J)
      (ThreeSum.ReportingHostWantedControls.record
        (ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w
          output)))
  (hlayout :
    Light.SegN μ dst
      (ThreeSum.ReportingHostWantedLayout.values
        (ThreeSum.LightReportingWantedLayout.layout dst h J K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC)))
  (hdecoded :
    ThreeSum.LightWantedDecode.Stored μ (ThreeSum.ReportingHostWantedLayout.decoded dst)
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) h J i output)
  (hcounter :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      dst)
  (hcounterRead : @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old))
  (hthreshold :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hends :
    ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (ThreeSum.LightReportingWantedAccess.selection n g rs
        (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
          (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w))
        pair bank cover NB NC h J (ThreeSum.LightBlockQuery.sourceCut h J) occ
        (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
          (ThreeSum.OutputDecodeRecords.layerCount h) J output))
      pair bank cover srcB srcC
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).b
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).c
      (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
        (ThreeSum.OutputDecodeRecords.layerCount h) J output)
      h J (ThreeSum.LightBlockQuery.sourceCut h J) counter)
  (hbank :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SourceBandBankData.finish bank NB NC g h J (ThreeSum.LightBlockQuery.sourceCut h J)) report)
  (hreport : @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankHeader.finish report h J NB NC g) counter)
  (hbuffers :
    ThreeSum.SharedReportingBankResourceBounds.WantedBuffers lim dst h J K
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC V)
  (hqueries :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat k K →
        ThreeSum.ReportingHostLevelData.Scratch lim h J k
          (ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output k)
          (@Finset.card.{0} (Fin NB)
            (ThreeSum.BandRawA.finiteBandPositions NB g
              (ThreeSum.BandRawA.ownerRecord n g rs
                  (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                    (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w))).b))
          (@Finset.card.{0} (Fin NC)
            (ThreeSum.BandRawA.finiteBandPositions NC g
              (ThreeSum.BandRawA.ownerRecord n g rs
                  (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                    (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w))).c))
          (ThreeSum.LightReportingWantedLayout.layout dst h J K
              (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC).maskBase
          (ThreeSum.LightReportingWantedLayout.layout dst h J K
              (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC).work)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hrecordSpace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightReportingWantedRecordCall.space (ThreeSum.ReportingHostWantedLayout.access dst J) dst cover counter
        h J K)
      lim.space)
  (hselectedWords :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
          (ThreeSum.ReportingHostWantedControls.record
            (ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w
              output))
          z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z) lim.word)
  (hguardWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w))
            threshold)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingTerminal.word h J)) lim.word)
  (hreadB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB j)) (fB j))
  (hreadC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC j)) (fC j))
  (hvaluesB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fB j)) lim.word)
  (hvaluesC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fC j)) lim.word)
  (htarget :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (ThreeSum.BandRawA.valueAt n g rs fA
                (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (fB j)))
          lim.word)
  (hcountWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NB NC))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (ThreeSum.SharedReportingBankResourceBounds.wantedDepth h J K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC))
      lim.depth),
  have S :=
    ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output;
  have D := ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output;
  Light.Meets lim ThreeSum.LightReportingWantedRecordCall.program
    (@OfNat.ofNat.{0} Nat (nat_lit 138) (instOfNatNat (nat_lit 138))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.ReportingHostWantedLayout.access dst J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter) (@List.nil.{0} Int)))))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@ThreeSum.LightReportingWanted.time.{0, 0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB)
        (Fin NC) (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J p
        shift (@ThreeSum.ReportingHostWantedOriginal.left h J n g rs fB w)
        (@ThreeSum.ReportingHostWantedOriginal.right h J n g rs fC w) S.NL S.NR old threshold
        (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w D K)
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Or
            (@LT.lt.{0} Nat instLTNat threshold
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                  (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w)))
            (ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w K)))
        (And
          (@Eq.{1} Int (ν counter)
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                  (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w))))
          (Light.KeptBut μ ν (ThreeSum.ReportingHostWantedLayout.packed dst J) counter
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @ThreeSum.LightReportingWantedRecord.program_meets_sourceProof

#print axioms solution
