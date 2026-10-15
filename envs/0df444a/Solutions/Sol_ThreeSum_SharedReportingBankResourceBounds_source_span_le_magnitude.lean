-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:41:38.364362+00:00
-- url     : https://prove2.me/submissions/d673e55e-9a17-4b9b-9c33-6edcce15723a

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
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




































































theorem overhead_bound (h J : ℕ) : LightBlockSourceRetainedHost.space 0 h J ≤
    J+2*(J*(512*h))+(J*(512*h)+1)^2+
      Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+20 := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space LightBlockSourceHashes.space
    LightSourceMaskFlags.space LightSourceRetainedStages.space LightPascal.tableSize
  omega

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


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000





































































































theorem source_span_le_magnitude_sourceProof (n : ℕ) :
    SourceBandBankLayout.span (half n) (blocks n) (2*half n*blocks n) ≤ 100*(magnitude n+1)^3 := by
  have H := components n
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hJ := H.blocksBound
  have hS := H.occurrence
  have hP := H.prime
  have hPP := H.primePower
  have hM := H.positive
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hcap := (downset_le_pow (width (half n) (blocks n)) (2*half n*blocks n)).trans hpower
  have hlogP : Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show 512*half n ≤ magnitude n by omega) hP
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hlogE : Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show width (half n) (blocks n) ≤ magnitude n by omega) hPP
    unfold LightBlockSourceBuild.endpointBound
    change Nat.log 2 (width (half n) (blocks n)*
      (LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n))+1) ≤ _
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hscratch := SourceBandBanksCosts.overhead_bound (half n) (blocks n)
  change LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤
    blocks n+2*width (half n) (blocks n)+(width (half n) (blocks n)+1)^2+
    Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1)+
    Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+20 at hscratch
  have hquad := Nat.pow_le_pow_left hW 2
  have hwork : LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ 30*(magnitude n+1)^2 := by
    nlinarith
  have hstride : LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2 ≤
      12*(magnitude n+1)^2 := by
    have hfamily := Nat.mul_le_mul hW hcap
    unfold LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
    nlinarith
  have hprod := Nat.mul_le_mul hS hstride
  rw [SourceBandBanksCosts.span_eq]
  change LightBlockSourceCatalog.count (half n) (blocks n)*
    (LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2)+
    downsetCap (width (half n) (blocks n)) (2*half n*blocks n)+width (half n) (blocks n)+2+
    LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ _
  nlinarith









































































































































end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat
    (ThreeSum.SourceBandBankLayout.span (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude_sourceProof

#print axioms solution
