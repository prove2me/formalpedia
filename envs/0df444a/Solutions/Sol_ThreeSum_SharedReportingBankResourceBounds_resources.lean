-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.resources
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:06:12.363351+00:00
-- url     : https://prove2.me/submissions/771891c1-cb08-4588-ba27-d7365b1bcb8c

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum_LightRadixKeys_space_bound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_offset_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys

open Light RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000






















theorem word_mono {p U j k : ℕ} (hj : j ≤ k) : word p U j ≤ word p U k := by
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ p+1) hj
  have hv := Nat.mul_le_mul_left U hpow
  have hpv := Nat.mul_le_mul_left p hv
  unfold word LightRadixRows.word
  omega

















































variable {lim : Limits} {P : Program}























































































































end ThreeSum.LightRadixKeys

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


























theorem count_pos (h k : ℕ) : 0 < count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
































































































































end ThreeSum.LightReportingPrefixCatalog

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


/-!
# The actual sorted index stays within polynomial mask-width overhead

Complete prefix catalogs have at most 2^(2W) records. This bounds both the
merge-sort logarithm and the binary-remainder scratch/time by the mask width,
so lookup contributes no linear factor in the catalog size to a query.
-/

namespace ThreeSum.ReportingHostCatalogIndexCosts

open Light ThreeSum.LightPascal

set_option maxHeartbeats 300000
























theorem sort_clog_le {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W :=
  Nat.clog_le_of_le_pow hn
























end ThreeSum.ReportingHostCatalogIndexCosts

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











































































































end ThreeSum.SharedReportingBankLevels

end

section


/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000































































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






























theorem levels_le (J : ℕ) : levels J ≤ J+1 := by
  have hh := level_le (show LightSwitchDepth.depth J ≤ LightSwitchDepth.depth J from le_rfl)
  unfold levels
  omega

theorem count_le {h J k : ℕ} (hk : k ≤ levels J) :
    LightReportingPrefixCatalog.count h k ≤ prefixCount h J :=
  ReportingHostPackedCatalog.prefix_count_le_pow (hk.trans (levels_le J))

theorem storage_le {h J k : ℕ} (hk : k ≤ levels J) : prefixSpan h k ≤ prefixStorage h J := by
  have hE : 1 ≤ localPairs h := by
    have hh := LightReportingPrefixCatalog.count_pos h 1
    exact Nat.succ_le_of_lt (by
      simpa only [LightReportingPrefixCatalog.count,pow_one,localPairs,localWidth] using hh)
  have hspace := LightRadixKeys.space_bound 0 (localPairs h) k hE
  have hcount := count_le (h := h) hk
  change (localPairs h)^k ≤ prefixCount h J at hcount
  have hspace' : prefixSpan h k ≤ (k+1)*((localPairs h)^k+1) := by
    simpa only [LightRadixKeys.space,Nat.zero_add,prefixSpan,LightReportingPrefixCatalog.count,localPairs,localWidth] using hspace
  exact hspace'.trans (Nat.mul_le_mul (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hcount 1))

theorem local_pairs_le (h : ℕ) : localPairs h ≤ 2^(2*(512*h)) := by
  simpa only [LightReportingPrefixCatalog.count,pow_one,localPairs,localWidth,Nat.one_mul] using
    (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) (J := 1) (k := 1) le_rfl)































theorem total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    total h J NB NC g ≤ LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((BandPartition.size_le NB g).trans hB))
    ((BandPartition.size_le NC g).trans hC)

theorem space_le {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.space free h J NB NC g ≤ free+extent h J n := by
  have hP := total_le (h := h) (J := J) (g := g) hB hC
  have ho := offset_le h J
  have hm := Nat.mul_le_mul_left (total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*levels J+levels J*cellBound h J) hP
  unfold LightSharedReportingHost.space
  apply max_le
  · unfold records LightPascal.tableSize extent
    omega
  · unfold SharedReportingBankHeader.finish rowBase payload records extent
    nlinarith

theorem index_word_mono {W a b : ℕ} (hab : a ≤ b) :
    LightReportingSortedCatalog.word W a ≤ LightReportingSortedCatalog.word W b := by
  have hm := Nat.mul_le_mul_left ((2^W)^2) (Nat.add_le_add_right hab 1)
  unfold LightReportingSortedCatalog.word LightReportingPackKeys.word
  omega

theorem resources_sourceProof {lim : Limits} {free h J NB NC g n d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (hspace : free+extent h J n ≤ lim.space)
    (hword : (word h J n g : ℤ) ≤ lim.word)
    (hdepth : d+depth h J ≤ lim.depth) :
    LightSharedReportingHost.Resources lim free h J NB NC g d := by
  have budget (x : ℕ) (hx : x ≤ word h J n g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hs := (space_le (free := free) (h := h) (J := J) (g := g) hB hC).trans hspace
  have hend : SharedReportingBankHeader.finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans hs
  have hNB := (BandPartition.size_le NB g).trans hB
  have hNC := (BandPartition.size_le NC g).trans hC
  have hmul := Nat.mul_le_mul_left (LightBlockSourceCatalog.count h J) hNB
  have hcount := count_le (h := h) (J := J) (k := levels J) le_rfl
  have hstorage := storage_le (h := h) (J := J) (k := levels J) le_rfl
  have hpowNonneg : (0 : ℤ) ≤ ((2^(512*h) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hpairPowNonneg : (0 : ℤ) ≤ ((2^(2*(512*h)) : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨hs,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,?_,?_⟩
  · unfold LightSharedReportingBank.controlWord word control
    omega
  · unfold word; omega
  · unfold word; omega
  · have he := local_pairs_le h
    unfold word
    omega
  · unfold word; omega
  · unfold depth at hdepth
    omega
  · intro q hq
    refine ⟨budget _ ?_,?_,budget _ ?_,?_,budget _ ?_,?_,?_,?_,?_,?_,?_⟩
    · unfold word stateWord
      omega
    · rw [rowBase_next]
      exact (rowBase_mono _ h J (levels J) (show q+1 ≤ total h J NB NC g from hq)).trans hend
    · unfold word; omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      apply budget
      have hh := LightRadixKeys.word_mono (p := 2^(512*h)) (U := 2^(512*h)) hkJ
      unfold word
      omega
    · unfold word width localWidth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := index_word_mono (W := width h J) (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      apply budget
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤ _
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤
        LightReportingSortedCatalog.word (width h J) (2^(2*width h J)) at hc
      unfold word
      omega
    · intro k hk
      have hv : (J-k)*(512*h) ≤ width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
      have hm := Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul_right g hp) (Nat.mul_le_mul_right g hp))
      apply budget
      unfold word
      omega
    · intro k hk
      have hr : SharedReportingBankLevels.residual h J k ≤ 2*h*J := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have ht := Nat.pow_le_pow_left (show J+SharedReportingBankLevels.residual h J k+1001 ≤ J+2*h*J+1001 by omega) 64
      apply budget
      change (J+SharedReportingBankLevels.residual h J k+1001)^64 ≤ _
      unfold word
      omega
    · unfold depth at hdepth
      omega
    · unfold depth width localWidth at hdepth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := ReportingHostCatalogIndexCosts.sort_clog_le (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      unfold depth width localWidth at hdepth
      omega

end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {lim : Light.Limits} {free h J NB NC g n d : Nat},
  @LE.le.{0} Nat instLENat NB n →
    @LE.le.{0} Nat instLENat NC n →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
            (ThreeSum.SharedReportingBankResourceBounds.extent h J n))
          lim.space →
        @LE.le.{0} Int Int.instLEInt
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.word h J n g)) lim.word →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                (ThreeSum.SharedReportingBankResourceBounds.depth h J))
              lim.depth →
            ThreeSum.LightSharedReportingHost.Resources lim free h J NB NC g d := by
  exact @ThreeSum.SharedReportingBankResourceBounds.resources_sourceProof

#print axioms solution
