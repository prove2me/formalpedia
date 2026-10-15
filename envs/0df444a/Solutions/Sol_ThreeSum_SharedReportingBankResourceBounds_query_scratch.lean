-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.query_scratch
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:32.325369+00:00
-- url     : https://prove2.me/submissions/46a049cf-f979-4547-aa1a-5f952ef6eb80

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
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
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
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

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


/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude

open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout














theorem succ_pow_bound {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  have hp := Nat.two_pow_pos e
  rw [pow_succ]
  omega




































































end ThreeSum.LightLocalCoverMagnitude

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
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0






















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _







noncomputable section









































































































































































































end
end ThreeSum.Switch

end

section


/-!
# Finite scalar bounds and minimality for the executed cubic switch

These are the exact cleared integer comparisons of `Switch.switchIndex`.
No real arithmetic is executed by the eventual program.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000































theorem index_le_residual {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    Switch.switchIndex J j r ≤ r :=
  (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1.trans (Nat.div_le_self _ _)
















end ThreeSum.LightSwitch

end

section


/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder

set_option maxHeartbeats 600000






















































































































theorem prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(512*h))) := by
  have hhalf : 2*h ≤ 512*h := by omega
  have he : LightReportingPrefixArrays.localCount (512*h) h ≤ 2^(2*(512*h)) := by
    calc
      _ ≤ 2^(512*h)*2^(2*h) := Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ ≤ 2^(512*h)*2^(512*h) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hhalf)
      _ = 2^(2*(512*h)) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (2^(2*(512*h)))^k := Nat.pow_le_pow_left he k
    _ = 2^(2*(k*(512*h))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(J*(512*h))) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk))

end ThreeSum.ReportingHostPackedCatalog

end

section


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000













theorem level_le {J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold LightSwitchDepth.depth at hk
  omega

















theorem switch_le {h J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) :
    switch h J k ≤ residual h J k :=
  LightSwitch.index_le_residual (candidates_nonempty hk)

theorem boxCut_le (h J k : ℕ) : boxCut h J k ≤ residual h J k := Nat.sub_le _ _





















































































end ThreeSum.SharedReportingBankLevels

end

section


/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition

open BandPartition SourceBandLayout






































theorem source_card (n g i : ℕ) : (source n g i).card=len n g i := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (equiv n g i)).symm

































end ThreeSum.SourceBandPartition

end

section


/-! # The shared source banks in the physical finite reporting domains -/

namespace ThreeSum.SourceBandFinite

open GlobalEncoding OutputDecodeRecords

theorem source_eq_finiteBandPositions (n g i : ℕ) :
    SourceBandPartition.source n g i=BandRawA.finiteBandPositions n g i := by
  ext t
  rw [SourceBandPartition.mem_source,BandRawA.mem_finiteBandPositions,BandRawA.mem_bandPositions]
























end ThreeSum.SourceBandFinite

end

section


/-! # Retained source pointers and complete source families precede the bank end -/

namespace ThreeSum.SharedReportingBankSources

open Light SubsetAddress BlockIndexedQuery GlobalEncoding































theorem source_card_le (n g i : ℕ) : (SourceBandPartition.source n g i).card ≤ g := by
  rw [SourceBandPartition.source_card]
  exact BandPartition.length_le n g i













end ThreeSum.SharedReportingBankSources

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


/-!
# Concrete scratch limits for queries into the retained shared catalog bank

One mask span of `2^W` works for every prescribed level. The remaining
workspace is polynomial in W, including the exact packed-key remainder
workspace. Both source cardinalities are bounded independently by the
physical band size, and the switch and cut are the executed bank values.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000








theorem query_items_le {c t : ℕ} (ht : t ≤ c) :
    LightSparseQuery.queryItems c t ≤ 2^c := by
  simpa only [LightSparseQuery.queryItems,downsetCap,Nat.min_eq_left ht,layerOffset_succ]
    using downset_le_pow c t

theorem query_lookup_word_mono {W a b : ℕ} (hab : a ≤ b) :
    LightReportingCatalogLookup.word W a ≤ LightReportingCatalogLookup.word W b := by
  have hmul := Nat.mul_le_mul_left (2^(2*W)) (Nat.add_le_add_right hab 1)
  unfold LightReportingCatalogLookup.word LightReportingCatalogLookup.valueBound
  omega

theorem query_lookup_log_le {W N : ℕ} (hN : N ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W N+1) ≤ 4*W+2 := by
  have hn := LightLocalCoverMagnitude.succ_pow_bound hN
  have hv : LightReportingCatalogLookup.valueBound W N ≤ 2^(4*W+1) := by
    calc
      _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hl := Nat.log_mono_right (b := 2) (LightLocalCoverMagnitude.succ_pow_bound hv)
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem query_band_card_le (n g i : ℕ) : (BandRawA.finiteBandPositions n g i).card ≤ g := by
  rw [← SourceBandFinite.source_eq_finiteBandPositions]
  exact SharedReportingBankSources.source_card_le n g i

theorem query_catalog_parameters {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J) :
    let D := SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
    D.t ≤ LightBlockQuery.residualSize h J k ∧
      D.boxCut ≤ LightBlockQuery.residualSize h J k ∧
      LightBlockQuery.residualSize h J k-D.t=D.boxCut := by
  change SharedReportingBankLevels.switch h J k ≤ (J-k)*(2*h) ∧
    SharedReportingBankLevels.boxCut h J k ≤ (J-k)*(2*h) ∧
    (J-k)*(2*h)-SharedReportingBankLevels.switch h J k=SharedReportingBankLevels.boxCut h J k
  rw [show (J-k)*(2*h)=SharedReportingBankLevels.residual h J k by
    unfold SharedReportingBankLevels.residual; ring]
  exact ⟨SharedReportingBankLevels.switch_le hk,SharedReportingBankLevels.boxCut_le h J k,rfl⟩

theorem query_masks_le {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J) :
    LightSparseQuery.queryItems (LightBlockQuery.residualSize h J k)
      (SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k).t ≤ queryMaskSpan h J := by
  have ht := (query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk).1
  have hv : BlockIndexedQuery.suffixStage J (512*h) k ≤ width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact (query_items_le ht).trans (Nat.pow_le_pow_right (by decide)
    (LightReportingSuffixBoxes.residual_le_suffix.trans hv))

theorem query_scratch_sourceProof {lim : Limits} {report h J NB NC g s i j k maskBase work : ℕ}
    (hk : k ≤ LightSwitchDepth.depth J)
    (hmasks : maskBase+queryMaskSpan h J ≤ work)
    (hspace : work+queryWorkSpan h J ≤ lim.space)
    (hword : (queryWord h J g : ℤ) ≤ lim.word) :
    ReportingHostLevelData.Scratch lim h J k
      (SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k)
      (BandRawA.finiteBandPositions NB g i).card
      (BandRawA.finiteBandPositions NC g j).card maskBase work := by
  let D := SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
  have hpar := query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hmask := query_masks_le (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hN := ReportingHostPackedCatalog.prefix_count_le_pow (h := h)
    (SharedReportingBankLevels.level_le hk)
  have hlog := query_lookup_log_le hN
  have hlookup := query_lookup_word_mono (W := width h J) hN
  have hv : BlockIndexedQuery.suffixStage J (512*h) k ≤ width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
  have hB := query_band_card_le NB g i
  have hC := query_band_card_le NC g j
  have hvalue : LightSparseQuery.magnitudeBound
      (BlockIndexedQuery.suffixStage J (512*h) k) (BlockIndexedQuery.suffixStage J (512*h) k)
      (LightBlockQuery.residualSize h J k) D.t
      (BandRawA.finiteBandPositions NB g i).card (BandRawA.finiteBandPositions NC g j).card ≤
      (2^(width h J)+1)*(2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g))) :=
    Nat.mul_le_mul (Nat.add_le_add_right hmask 1)
      (Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul hp hB) (Nat.mul_le_mul hp hC)))
  have budget (x : ℕ) (hx : x ≤ queryWord h J g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  refine ⟨(Nat.add_le_add_left hmask maskBase).trans hmasks,?_,?_,?_,
    budget _ ?_,budget _ ?_,budget _ ?_,by omega,hpar.2.1,hpar.2.2.le⟩
  · unfold queryWorkSpan at hspace
    unfold LightPascal.tableSize
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWorkSpan at hspace
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWorkSpan at hspace
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    dsimp only [SharedReportingBankLayout.width,SharedReportingBankLayout.localWidth,LightBlockQuery.width] at *
    omega
  · unfold queryWord
    exact hvalue.trans (Nat.le_add_left _ _)

end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {lim : Light.Limits} {report h J NB NC g s i j k maskBase work : Nat},
  @LE.le.{0} Nat instLENat k (ThreeSum.LightSwitchDepth.depth J) →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
          (ThreeSum.SharedReportingBankResourceBounds.queryMaskSpan h J))
        work →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
            (ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan h J))
          lim.space →
        @LE.le.{0} Int Int.instLEInt
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.queryWord h J g)) lim.word →
          ThreeSum.ReportingHostLevelData.Scratch lim h J k
            (ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k)
            (@Finset.card.{0} (Fin NB) (ThreeSum.BandRawA.finiteBandPositions NB g i))
            (@Finset.card.{0} (Fin NC) (ThreeSum.BandRawA.finiteBandPositions NC g j)) maskBase work := by
  exact @ThreeSum.SharedReportingBankResourceBounds.query_scratch_sourceProof

#print axioms solution
