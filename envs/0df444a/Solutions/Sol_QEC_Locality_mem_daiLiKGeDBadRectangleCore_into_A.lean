-- Prove2me | solution 1 for QEC.Locality.mem_daiLiKGeDBadRectangleCore_into_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:21:23.741999+00:00
-- url     : https://prove2.me/submissions/80101b57-8128-4e4f-b603-6a26f179d2ec

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_eq_get
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_into_A

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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hCandidate : Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - ell ∧
        ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by
  have hCore : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles
      (Sum.inr (cell, slot)) := by
    change q ∈ (embedding.qubitsInRectangle
      (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
        (Sum.inr (cell, slot))).1
      (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
        (Sum.inr (cell, slot))).2).filter _
    rw [daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell slot hSlot]
    exact Finset.mem_filter.mpr ⟨hRect, ⟨hNotSeparator, hStrict⟩⟩
  exact mem_daiLiKGeDRegionCore_into_A P embedding d threshold w ell t cells rectangles
    (Sum.inr (cell, slot)) hCandidate q hCore
end QEC.Locality
