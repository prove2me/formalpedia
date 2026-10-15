-- Prove2me | solution 1 for ThreeSum.ReportingHostLevelData.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:26.192432+00:00
-- url     : https://prove2.me/submissions/aa77dd10-d4c9-45c7-9a86-f7d9850cb877

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
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
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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


/-!
# Exact retained catalog and scratch interfaces for the level loop

These records collect the memory assertions already produced by the actual
prefix-catalog constructor. They contain no assumed query procedure. The
query adapter below invokes the existing closed, verified catalog program.
-/

namespace ThreeSum.ReportingHostLevelData

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false













variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]






















































theorem Stored.of_kept_sourceProof {h J k baseL baseR stop : ℕ} {μ ν : ℕ→ℤ} {D : Catalog} {hk : k≤J}
    {pMod shift : ℤ} {B : Finset β} {C : Finset γ} {b : β→ℤ} {c : γ→ℤ} {q : GlobalOutput h J}
    (H : Stored μ D hk pMod shift B C b c q) (HB : Bounds h J k D baseL baseR stop)
    (hkeep : Kept μ ν stop) : Stored ν D hk pMod shift B C b c q := by
  obtain ⟨S,hs,hperm,hsort⟩ := H.index
  have hlen : S.length=count h k := hperm.length_eq.trans (ReportingHostPackedCatalog.codes_length _ _)
  constructor
  · refine ⟨S,?_,hperm,hsort⟩
    intro i hi
    exact (hkeep _ (by rw [hlen] at hi; have hh:=HB.index; omega)).trans (hs i hi)
  · intro i hi
    have hi' : i<count h k := by simpa only [List.length_map,List.length_ofFn] using hi
    exact (hkeep _ (by have hh:=HB.pointers; omega)).trans (H.pointers i hi)
  · intro i hi
    exact ReportingHostQueryBounds.boxStored_of_on (H.boxes i hi) (by
      intro u _ hu
      exact hkeep u (hu.trans_le (ReportingHostCatalogSelection.selected_box_end hi HB.boxes)))

























end ThreeSum.ReportingHostLevelData

end

universe u_2 u_3

theorem solution : ∀ {β : Type u_2} {γ : Type u_3} [Fintype.{u_2} β] [Fintype.{u_3} γ] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ]
  {h J k baseL baseR stop : Nat} {μ ν : Nat → Int} {D : ThreeSum.ReportingHostLevelData.Catalog}
  {hk : @LE.le.{0} Nat instLENat k J} {pMod shift : Int} {B : Finset.{u_2} β} {C : Finset.{u_3} γ} {b : β → Int}
  {c : γ → Int} {q : ThreeSum.GlobalEncoding.GlobalOutput h J},
  @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J k μ D hk pMod shift B C b c q →
    ThreeSum.ReportingHostLevelData.Bounds h J k D baseL baseR stop →
      Light.Kept μ ν stop → @ThreeSum.ReportingHostLevelData.Stored.{u_2, u_3} β γ h J k ν D hk pMod shift B C b c q := by
  exact @ThreeSum.ReportingHostLevelData.Stored.of_kept_sourceProof

#print axioms solution
