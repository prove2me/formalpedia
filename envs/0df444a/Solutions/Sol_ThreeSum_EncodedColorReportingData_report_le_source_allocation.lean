-- Prove2me | solution 1 for ThreeSum.EncodedColorReportingData.report_le_source_allocation
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:38:36.761402+00:00
-- url     : https://prove2.me/submissions/b0fcb7f6-2a43-43b3-83b9-a6443f90464b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorResources_pipeline_space_bound
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_count_le_encoderCount


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
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
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys

section


/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]



theorem sum_correlation (F H : G → ℕ) :
    (∑ d, correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, sum_correlation] at hs
  exact (lt_irrefl _ hs)























end ThreeSum.Balancing

end

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
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000


































































































theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]































end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega


















































































































































end ThreeSum.BandCandidateRows

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition












theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega

/-- A finite ceiling bound, including the empty input. -/
theorem size_mul_le (n g : ℕ) : size n g*g ≤ n+g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hd := Nat.div_mul_le_self (n-1) g
    simp only [size,if_neg hn,Nat.add_mul,Nat.one_mul]
    omega

























theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

end

section


/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open Finset
open scoped BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]




theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp



















































































end ThreeSum.Histograms

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





























theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by
  rw [row_length]
  split_ifs
  · exact BandPartition.length_le n g r.a
  · omega










theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]







theorem count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [count_succ]
    have hh := row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length

























































































end ThreeSum.BandRawA

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












































































































end ThreeSum.LightResidues

end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J




section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

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












theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, signedHistogram p c values n z) = n := by
  unfold signedHistogram
  rw [Histograms.sum_histogram]
  simp















































































































































end ThreeSum.LightResidueHistogram

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




theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]
































































end ThreeSum.LightCoverKeyData

end

section


/-!
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators







theorem offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * Balancing.correlation F H (offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by
  obtain ⟨z, hz⟩ := Balancing.exists_balanced_offset F H
  have hmin := LightMinimum.least_value_le
    (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p z.val (ZMod.val_lt z)
  have hminNat : Balancing.correlation F H (offset F H : ZMod p) ≤
      Balancing.correlation F H z := by
    simpa only [offset, ZMod.natCast_zmod_val, Nat.cast_le] using hmin
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at hz
  exact (Nat.mul_le_mul_left p hminNat).trans hz








variable {lim : Limits} {P : Program} {d : ℕ}






































































end ThreeSum.LightBalancedOffset

end

section


/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000








/-- The actual selected offset satisfies the exact raw-incidence mean bound,
including duplicate keys in either original array. -/
theorem selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by
  have h := LightBalancedOffset.offset_balanced (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)
  rw [sum_signedHistogram,sum_signedHistogram] at h
  change p * Balancing.correlation _ _ (selected p left right nLeft nRight : ZMod p) ≤ _ at h
  unfold signedHistogram at h
  rw [Histograms.correlation_histograms] at h
  simpa only [one_mul,Nat.mul_comm] using h













































variable {lim : Limits} {P : Program} {d : ℕ}








































































































































end ThreeSum.LightOriginalOffset

end

section


/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset

open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators

set_option maxHeartbeats 1800000




















































theorem residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,sub_eq_zero]
  constructor
  · intro hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  · intro hh
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hh.symm







end ThreeSum.GlobalKeyOffset

end

section


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000






















theorem keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by
  rw [keys,List.length_map,records_length]











































































































end ThreeSum.RawAKeyLists

end

section


/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs

open Light SourceBuckets
open scoped BigOperators

set_option maxHeartbeats 1200000























































































































theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    LightResidues.residue M 1 b=LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),LightResidues.residue_cast hM,
    LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







































end ThreeSum.WantedPairs

end

section


/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys

open Light
open scoped BigOperators



theorem code_eq_residue (M : ℕ) (shift x : ℤ) :
    code M shift x=LightResidues.residue M 1 (x+shift) := by
  simp only [code,LightSourceResidues.key,LightResidues.residue,one_mul]
  congr 1
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]




theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    code M 0 b=code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [code_eq_residue,code_eq_residue,add_zero]
  exact WantedPairs.residue_eq_iff hM a b shift




theorem total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    total M left right NL NR shift =
      Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by
  unfold total WantedPairs.count LightHistogram.count Histograms.pairMass
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,one_mul,
    code_eq_iff hM,GlobalKeyOffset.residue_relation_iff]

theorem selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by
  rw [total_eq_pairMass M (Nat.pos_of_ne_zero (NeZero.ne M))]
  simpa only [Int.cast_natCast] using LightOriginalOffset.selected_pairMass_bound M left right NL NR



















end ThreeSum.WantedResidueKeys

end

section


/-!
# Executable balancing followed by the complete wanted-pair join

The host chooses the common shift from the two original signed arrays and
then builds every matching original-position pair. The returned count obeys
the exact incidence mean bound. The offset and the residue/bucket inputs are
computed by the closed program, with the same duplicate multiplicities.
-/

namespace ThreeSum.LightBalancedWanted

open Light WantedResidueKeys

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

























variable {lim : Limits}



























































theorem total_le_div (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR/M := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne M))).mpr
  simpa only [Nat.mul_comm] using selected_total_bound M left right NL NR













end ThreeSum.LightBalancedWanted

end

section


/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000








































theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl






















variable {lim : Limits}






















































































end ThreeSum.LightGuardedWanted

end

section


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets































theorem capacity_product_le (n g : ℕ) (hg : 0 < g) : size n g*cap n g ≤ 2*n := by
  by_cases hgn : g ≤ n
  · rw [cap,min_eq_right hgn]
    exact (size_mul_le n g).trans (by omega)
  · by_cases hn : n=0
    · simp [hn,cap]
    · have hdiv : (n-1)/g=0 := Nat.div_eq_of_lt (by omega)
      simp only [cap,min_eq_left (by omega : n ≤ g),size,if_neg hn,hdiv,zero_add,one_mul]
      omega





























theorem work_bound (base n g m : ℕ) (hg : 0 < g) :
    work base n g m ≤ base+4*n+size n g*(3*m+7) := by
  have hc := capacity_product_le n g hg
  unfold work hist data stride
  nlinarith









































end ThreeSum.SourceBandLayout

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

theorem bands_modulus_le_encoderCount (n : ℕ) :
    bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*tableCount n := Nat.mul_le_mul_left _ (modulus_le_tableCount n)
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : bandCount n ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) :=
      Nat.le_mul_of_pos_right _ (BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := bands_modulus_le_encoderCount n

theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by
  apply (BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,BandPartition.size]
  · have hg := bandSize_pos n
    have hb := (bandCount_mul_bounds n).1
    have hb' : n ≤ bandCount n*bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/bandSize n < bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [BandPartition.size,if_neg hn]
    omega

















theorem persistent_space_le_encoderCount {base N n : ℕ} (hN : N ≤ n) :
    SourceBandLayout.work base N (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+14*encoderCount n := by
  have hs := SourceBandLayout.work_bound base N (bandSize n)
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  nlinarith

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











theorem next_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    next base NL NR (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+29*encoderCount n+9 := by
  have hl := SourceBandCosts.persistent_space_le_encoderCount (base := leftBase base) hNL
  have hr := SourceBandCosts.persistent_space_le_encoderCount
    (base := rightBase base NL (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)))) hNR
  have hm := modulus_le_encoderCount hn
  change rightBase base NL (bandSize n) _ ≤ _ at hl
  change zeroBase base NL NR (bandSize n) _ ≤ _ at hr
  unfold next leftBase at *
  omega

end ThreeSum.SourceBandPairCosts

end

section


/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress














theorem count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n :=
  max_le (SourceBandCosts.size_le_bandCount hNL) (SourceBandCosts.size_le_bandCount hNR)





































































theorem finish_eq (base NL NR g h J cut : ℕ) :
    SourceBandBankData.finish base NL NR g h J cut=
      base+5+SourceBandPairSlices.count NL NR g*SourceBandBankLayout.span h J cut := rfl








































theorem finish_le_encoderCount {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandBankData.finish base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+5+storageFactor n*encoderCount n := by
  rw [finish_eq]
  exact Nat.add_le_add_left (span_count_le_encoderCount (count_le_bandCount hNL hNR)) _











end ThreeSum.SourceBandBanksCosts

end

section


/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts

open Scales TrimScales StageBounds CostLedger BandScales











theorem scheduleCount_le_encoderCount {n : ℕ} (hn : 0 < n) : scheduleCount n ≤ encoderCount n := by
  have hf : 0 < fullOutputs n :=
    (typedOutputs_pos n).trans_le (SourceBandCosts.typedOutputs_le_fullOutputs n)
  have hs : scheduleCount n ≤ tableCount n := Nat.le_mul_of_pos_right _ hf
  exact hs.trans (SourceBandPairCosts.tableCount_le_encoderCount hn)

theorem occurrenceRows_le_encoderCount {n : ℕ} (hn : 0 < n) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*blockCount (inputBits n) ≤
      blockCount (inputBits n)*encoderCount n := by
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  have h := Nat.mul_le_mul_right (blockCount (inputBits n)) (scheduleCount_le_encoderCount hn)
  simpa only [Nat.mul_comm] using h

theorem bankHeader_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      base+(29+blockCount (inputBits n))*encoderCount n+9 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hr := occurrenceRows_le_encoderCount hn
  unfold LightSourceBandHost.bankHeader LightSourceBandHost.occurrenceBase
  nlinarith

theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+14 := by
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.finish_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hNL hNR
  unfold LightSourceBandHost.finish
  nlinarith



















end ThreeSum.SourceBandHostCosts

end

section


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds
















theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.count nA nB nC g ≤ LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := BandPartition.size_mono (g := g) ha
  have b := BandPartition.size_mono (g := g) hb
  have c := BandPartition.size_mono (g := g) hc
  unfold LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)






























































end ThreeSum.EncodedColorPrimeCosts

end

section


/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
















theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by
  have h := EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : LightEncodedColorPrime.count n n n g=ColorBandBounds.count n g := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [sortedRecords, BandCandidateRows.records_length]
  exact h

theorem incidences_length_le {A B C : List ℤ} {n : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (incidences n A B C hsA hsB hsC).length ≤ bandSize n*ColorBandBounds.count n (bandSize n) := by
  unfold incidences
  rw [values_length]
  exact (items_length_le ..).trans (Nat.mul_le_mul_left _ (records_length_le ha hb hc))






















end ThreeSum.EncodedColorNormalizedData

end

section


/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts

open Scales TrimScales StageBounds CostLedger BandScales











































theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 := by
  have hs := SourceBandHostCosts.finish_le_encoderCount (base := base+3) hn hNL hNR
  unfold LightSourceControlsHost.finish LightSourceControlsHost.sourceBase
  omega




















end ThreeSum.SourceControlCosts

end

section


/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts

open Scales TrimScales StageBounds CostLedger BandScales





































theorem finish_le {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ finish base n :=
  SourceControlCosts.finish_le_encoderCount hn hNL hNR






end ThreeSum.SourceFiniteCosts

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


/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts

open Light WantedResidueKeys

set_option maxHeartbeats 1800000

































theorem sourceBase_eq (free M h J len : ℕ) :
    sourceBase free M h J len=LightCoverKeyData.keyEnd free h J+
      6*len+2*LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*LightGuardedWanted.totalKeys h J/M) := by
  unfold sourceBase LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightGuardedWanted.wantedFree
  omega

theorem sourceBase_le (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J) ≤
        sourceBase free M h J xs.length := by
  have h := LightBalancedWanted.total_le_div M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
  rw [LightGuardedWanted.selected_eq] at h
  unfold EncodedColorWantedData.nextFree sourceBase
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _













theorem sourceBase_mono {free M h J len len' : ℕ} (hlen : len ≤ len') :
    sourceBase free M h J len ≤ sourceBase free M h J len' := by
  rw [sourceBase_eq,sourceBase_eq]
  gcongr

























end ThreeSum.EncodedColorWantedCosts

end

section


/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts

open Scales BandScales ArithmeticStageBounds



































theorem base_le {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    LightEncodedColorFiniteSources.base free n p M xs ≤ sourceBase free n M len :=
  (EncodedColorWantedCosts.sourceBase_le free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs).trans (EncodedColorWantedCosts.sourceBase_mono hlen)


























theorem finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ SourceFiniteCosts.finish bound n := by
  apply (SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold SourceFiniteCosts.finish
  omega












end ThreeSum.EncodedColorStageCosts

end

section


/-!
# The original source header after shared reporting and dense initialization

The prelude returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩
























theorem report_le_source_allocation_sourceProof {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    reportBase free n A B C hsA hsB hsC ≤ free+(EncodedColorResources.need n U).cells := by
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  have hlen := EncodedColorNormalizedData.incidences_length_le
    (hsA := hsA) (hsB := hsB) (hsC := hsC) ha hb hc
  have hbase : EncodedColorPipelineData.controls free n A B C hsA hsB hsC ≤
      LightEncodedColorPipeline.sourceBound free n := EncodedColorStageCosts.base_le hlen
  have hfinish : EncodedColorPipelineData.finish free n A B C hsA hsB hsC ≤
      LightEncodedColorPipeline.finishBound free n := EncodedColorStageCosts.finish_le hn hbase hb hc
  have hs : LightEncodedColorPipeline.finishBound free n+8 ≤ LightEncodedColorPipeline.space free n U :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hall := (Nat.add_le_add_right hfinish 8).trans (hs.trans (EncodedColorResources.pipeline_space_bound free n U))
  simpa only [reportBase,EncodedColorResources.need,Nat.add_assoc] using hall





















end ThreeSum.EncodedColorReportingData

end


theorem solution : ∀ {μ : Nat → Int} {free n : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) (U : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
      (ThreeSum.EncodedColorResources.need n U).cells) := by
  exact @ThreeSum.EncodedColorReportingData.report_le_source_allocation_sourceProof

#print axioms solution
