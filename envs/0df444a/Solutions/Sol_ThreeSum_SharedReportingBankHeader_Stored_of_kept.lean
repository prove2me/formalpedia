-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:54.01952+00:00
-- url     : https://prove2.me/submissions/f56a1f07-a50d-47c1-9ead-f1cd267cad03

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
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
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
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


/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds

open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators











































theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*downsetCap W cut+subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds

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







theorem codes_length (key : ℕ → ℕ) (n : ℕ) : (codes key n).length=n := by simp [codes]



























































































































end ThreeSum.ReportingHostPackedCatalog

end

section


/-!
# Exact original valid-prefix selection from the complete physical catalog

The index is a proof witness for the actual unique stored mask pair. It is not
an argument supplied to the querying machine: the physical sorted lookup
recovers it from the two original prefix masks.
-/

namespace ThreeSum.ReportingHostCatalogSelection

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog











variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
































theorem selected_box_end {N i boxBase boxCut V upper : ℕ} (hi : i < N)
    (hboxes : boxBase+N*stride V boxCut ≤ upper) :
    boxBase+i*stride V boxCut+(V+1)*downsetCap V boxCut ≤ upper := by
  have hm := Nat.mul_le_mul_right (stride V boxCut) (show i+1 ≤ N by omega)
  have hm' : i*stride V boxCut+stride V boxCut ≤ N*stride V boxCut := by
    simpa only [Nat.add_mul,Nat.one_mul] using hm
  change boxBase+i*stride V boxCut+stride V boxCut ≤ upper
  omega

end ThreeSum.ReportingHostCatalogSelection

end

section


/-! # Exact retained cells of one shared reporting catalog -/

namespace ThreeSum.SharedReportingBankData

open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000

































theorem Tables.of_kept {h J k bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Tables μ D hk f g)
    (heq : Kept μ ν bound) (hindex : D.indexBase+count h k ≤ bound)
    (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Tables ν D hk f g := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  have hlen : S.length=count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  refine ⟨⟨S,?_,hperm,hsort⟩,?_,?_⟩
  · intro i hi
    exact (heq _ (by rw [hlen] at hi; omega)).trans (hs i hi)
  · intro i hi
    have hi' : i < count h k := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (heq _ (by omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi) (by
      intro a _ ha
      exact heq a (ha.trans_le (ReportingHostCatalogSelection.selected_box_end hi hbox)))

theorem Entry.of_kept {h J k record bound : ℕ} {μ ν : ℕ → ℤ} {D : Catalog} {hk : k ≤ J}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Entry μ record D hk f g)
    (heq : Kept μ ν bound) (hrecord : record+5 ≤ bound)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_kept heq hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ (by omega)).trans (H.header i hi)










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


/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000













theorem records_le_payload (free h J NB NC g : ℕ) :
    records free ≤ payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _























theorem levels_of_kept {μ ν : ℕ → ℤ} {record base h J K bound : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g) (heq : Kept μ ν bound)
    (hrecord : record+5*K ≤ bound) (hbase : baseAt base h J K ≤ bound) :
    Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hbase
  refine ⟨hkJ,Hk.of_kept heq (by omega) (hend.1.trans hbefore)
    (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩






theorem Stored.of_kept_sourceProof {μ ν : ℕ → ℤ} {free h J NB NC g bound : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift) (heq : Kept μ ν bound)
    (hbound : finish free h J NB NC g ≤ bound) : Stored ν free h J NB NC g fB fC p shift := by
  have hmeta := (records_le_payload free h J NB NC g).trans
    ((payload_le_finish free h J NB NC g).trans hbound)
  refine ⟨?_,?_⟩
  · intro i hi
    have hi' : i < 9 := by simpa [SegN,header] using hi
    exact (heq _ (by unfold records at hmeta; omega)).trans (H.heads i hi)
  · intro s hs i hi j hj hr
    have Hrow := H.rows s hs i hi j hj hr
    apply levels_of_kept Hrow heq
    · have hh := Nat.mul_le_mul_left (5*levels J) (show
        rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by omega)
      have hp := (payload_le_finish free h J NB NC g).trans hbound
      unfold rowRecord payload at *
      nlinarith
    · rw [rowBase_next]
      exact (rowBase_mono _ h J (levels J) (show
        rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by omega)).trans hbound















end ThreeSum.SharedReportingBankHeader

end


theorem solution : ∀ {μ ν : Nat → Int} {free h J NB NC g bound : Nat} {fB fC : Nat → Int} {p shift : Int},
  ThreeSum.SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift →
    Light.Kept μ ν bound →
      @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankHeader.finish free h J NB NC g) bound →
        ThreeSum.SharedReportingBankHeader.Stored ν free h J NB NC g fB fC p shift := by
  exact @ThreeSum.SharedReportingBankHeader.Stored.of_kept_sourceProof

#print axioms solution
