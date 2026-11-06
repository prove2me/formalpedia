-- Prove2me | solution 1 for QEC.Locality.horizontalRectangleQubits_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:44:46.479342+00:00
-- url     : https://prove2.me/submissions/3e501cc2-479e-4090-a692-1fb686e7222b

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (lowerHorizontalRectangleQubits embedding lower upper cut)
      (upperHorizontalRectangleQubits embedding lower upper cut) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hqLower : (embedding.point q).2 ≤ cut := by
    exact (Finset.mem_filter.mp hLower).2
  have hqUpper : cut < (embedding.point q).2 := by
    exact (Finset.mem_filter.mp hUpper).2
  exact (not_lt_of_ge hqLower) hqUpper
end QEC.Locality
