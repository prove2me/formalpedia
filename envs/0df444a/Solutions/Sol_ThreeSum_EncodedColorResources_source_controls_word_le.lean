-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.source_controls_word_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:09:12.048986+00:00
-- url     : https://prove2.me/submissions/fecc2de3-f787-4df4-8574-e1830abfe1e0

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_EncodedColorResources_schedule_power_le
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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






































































































































































































































@[simp] theorem layerOffset_zero (L : ℕ) : layerOffset L 0 = 0 := by
  simp [layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _



















































theorem enumerateThrough_length (L k : ℕ) :
    (enumerateThrough L k).length = layerOffset L (k + 1) := by
  induction k with
  | zero => simp [enumerateThrough, enumerateLayer_length, layerOffset_succ]
  | succ k ih =>
      rw [enumerateThrough, List.length_append, ih, enumerateLayer_length,
        layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (enumerateDownset L cut).length = downsetCap L cut :=
  enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ enumerateThrough L k ↔ m < 2 ^ L ∧ weight L m ≤ k := by
  induction k with
  | zero => simp [enumerateThrough, mem_enumerateLayer, IsMask]
  | succ k ih =>
      simp only [enumerateThrough, List.mem_append, ih, mem_enumerateLayer, IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ enumerateDownset L cut ↔ m < 2 ^ L ∧ weight L m ≤ cut := by
  rw [enumerateDownset, mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (weight_le_width hm)⟩

theorem enumerateThrough_nodup (L k : ℕ) : (enumerateThrough L k).Nodup := by
  induction k with
  | zero => exact enumerateLayer_nodup L 0
  | succ k ih =>
      apply ih.append (enumerateLayer_nodup L (k + 1))
      intro m hm hn
      have ht := (mem_enumerateThrough L k m).mp hm
      have hk := (mem_enumerateLayer L (k + 1) m).mp hn
      have hw := hk.2
      omega

theorem enumerateDownset_nodup (L cut : ℕ) : (enumerateDownset L cut).Nodup :=
  enumerateThrough_nodup L (min cut L)




























































































































end ThreeSum.SubsetAddress

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







theorem work_address (base count W cut : ℕ) :
    LightBlockSourceBatchLayout.work base count W cut =
      base+count*(stride W cut+2)+downsetCap W cut+W+2 := by
  unfold LightBlockSourceBatchLayout.work rowOut bitBase maskBase slot banks
  ring
























































































end ThreeSum.BlockSourceCatalogCosts

end

section


/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder











theorem host_space_add (base free h J : ℕ) :
    LightBlockSourceRetainedHost.space (base+free) h J=
      base+LightBlockSourceRetainedHost.space free h J := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
  omega





































































end ThreeSum.SourceBandBankLayout

end

section


/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress












































































theorem span_eq (h J cut : ℕ) : SourceBandBankLayout.span h J cut=
    LightBlockSourceCatalog.count h J*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut+2)+
      downsetCap (J*(512*h)) cut+J*(512*h)+2+LightBlockSourceRetainedHost.space 0 h J := by
  unfold SourceBandBankLayout.span
  have h := SourceBandBankLayout.host_space_add
    (LightBlockSourceBatchLayout.work 0 (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) 0 h J
  simp only [Nat.add_zero] at h
  rw [h,BlockSourceCatalogCosts.work_address]
  omega




























































end ThreeSum.SourceBandBanksCosts

end

section


/-! # Arithmetic dimensions of the original shared source bank -/

namespace ThreeSum.SourceControlLayout

open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress












theorem scratch_eq (h J : ℕ) :
    scratch J (J*(512*h)) (Nat.log 2 ((512*h)*localPrime h+1))
      (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      LightBlockSourceRetainedHost.space 0 h J := by
  unfold scratch LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
    LightPascal.tableSize
  omega

theorem stride_eq (W cut : ℕ) :
    stride W (downsetCap W cut)=LightBlockSourceBatchLayout.stride W cut+2 := by
  unfold stride LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
  ring

theorem span_eq (h J cut : ℕ) :
    span J (J*(512*h)) (downsetCap (J*(512*h)) cut) (LightBlockSourceCatalog.count h J)
      (Nat.log 2 ((512*h)*localPrime h+1)) (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      SourceBandBankLayout.span h J cut := by
  unfold span
  rw [scratch_eq,stride_eq,SourceBandBanksCosts.span_eq]




end ThreeSum.SourceControlLayout

end

section


/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000






















theorem downset_le_pow (W cut : ℕ) : downsetCap W cut ≤ 2^W := by
  have hn := enumerateDownset_nodup W cut
  have hsub : (enumerateDownset W cut).toFinset ⊆ Finset.range (2^W) := by
    intro m hm
    exact Finset.mem_range.mpr ((mem_enumerateDownset W cut m).mp (List.mem_toFinset.mp hm)).1
  have hc := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hn,enumerateDownset_length] using hc




























































































































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (half n) (blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (half n))).trans (powers n).2.2.1

theorem endpoint_le (n : ℕ) : LightBlockSourceBuild.endpointBound (half n) (blocks n) ≤ (scale n)^2 := by
  have hw : width n ≤ scale n := by have hh := (dimensions n).1; omega
  have hh := Nat.mul_le_mul hw (powers n).2.2.1
  simpa only [LightBlockSourceBuild.endpointBound,width,BlockSourceEncoding.modulus,pow_two] using hh
















































noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section


/-! # Finite space and word bounds for the actual retained source constructors -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open SubsetAddress CostLedger TrimScales

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
























































































theorem source_span_le (n : ℕ) : SourceBandBankLayout.span (half n) (blocks n) (mu n) ≤ 100*(scale n)^3 := by
  have hm : SharedReportingBankResourceBounds.magnitude n+1 ≤ scale n := by unfold scale; omega
  have hs := SharedReportingBankResourceBounds.source_span_le_magnitude n
  rw [show 2*SharedReportingBankResourceBounds.half n*SharedReportingBankResourceBounds.blocks n=mu n from
    BlockSourceSharing.cutoff_eq n] at hs
  exact hs.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hm 3))

theorem source_controls_word_le_sourceProof (n : ℕ) : LightSourceControls.word (half n) (blocks n) (mu n) ≤ 200*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hW := (dimensions n).1
  have hJ := (dimensions n).2.1
  have hcut := (dimensions n).2.2.1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hS := H.rounds
  have hocc := (powers n).2.1
  have hPP := (powers n).2.2.1
  have hmod := modulus_le n
  have hE := endpoint_le n
  have hpow := (powers n).1
  have hpow0 : 2^(width n) ≤ scale n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hpow
  have hK := (SharedReportingBankResourceBounds.downset_le_pow (width n) (mu n)).trans hpow0
  have hstrideProd := Nat.mul_le_mul hW hK
  have hstride : SourceControlLayout.stride (width n) (downsetCap (width n) (mu n)) ≤ 10*(scale n)^2 := by
    unfold SourceControlLayout.stride
    nlinarith only [hb,hW,hK,hstrideProd]
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hlogP := Nat.log_le_self 2 ((512*half n)*localPrime (half n)+1)
  have hlogE := Nat.log_le_self 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)
  have hquad := Nat.pow_le_pow_left hW 2
  have hspan := source_span_le n
  have hspanWord : LightSourceControls.spanWord (half n) (blocks n) (mu n) ≤ 150*(scale n)^3 := by
    unfold LightSourceControls.spanWord SourceControlLayout.word
    rw [SourceControlLayout.span_eq]
    change SourceBandBankLayout.span (half n) (blocks n) (mu n)+
      SourceControlLayout.stride (width n) (downsetCap (width n) (mu n))+blocks n+width n+
      downsetCap (width n) (mu n)+LightBlockSourceCatalog.count (half n) (blocks n)+
      Nat.log 2 ((512*half n)*localPrime (half n)+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+(width n+1)^2+30 ≤ _
    nlinarith only [hb,hspan,hstride,hJ,hW,hK,hocc,hlogP,hlogE,hLP,hE,hquad]
  have hwp := Nat.mul_le_mul hW hpow
  have hSwhole := schedule_power_le n
  unfold LightSourceControls.word
  change LightSourceControls.spanWord (half n) (blocks n) (mu n)+(width n+1)*2^(width n+1)+
    (scheduleSize (half n)+1)^(blocks n+1)+2*((512*half n)*localPrime (half n)+1)+
    2*(LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+
    localPrime (half n)^(blocks n)*localPrime (half n)+blocks n+512*half n+localPrime (half n)+
    mu n+scheduleSize (half n)+BlockSourceEncoding.modulus (half n) (blocks n)+width n+50 ≤ _
  nlinarith only [hb,hspanWord,hwp,hSwhole,hLP,hE,hPP,hJ,hL,hP,hcut,hS,hmod,hW]




























































end ThreeSum.EncodedColorResources

end


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat
    (ThreeSum.LightSourceControls.word (ThreeSum.EncodedColorResources.half n) (ThreeSum.EncodedColorResources.blocks n)
      (ThreeSum.Scales.mu n))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.EncodedColorResources.scale n) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @ThreeSum.EncodedColorResources.source_controls_word_le_sourceProof

#print axioms solution
