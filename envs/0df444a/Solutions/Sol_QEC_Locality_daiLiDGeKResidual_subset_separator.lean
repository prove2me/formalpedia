-- Prove2me | solution 1 for QEC.Locality.daiLiDGeKResidual_subset_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:32:33.587459+00:00
-- url     : https://prove2.me/submissions/8d350c70-4230-4fc5-8916-80aec3719a5c

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeK_assignment

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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ⊆
      daiLiDGeKSeparator P embedding threshold w ell t := by
  intro q hq
  have hOutside := (Finset.mem_sdiff.mp hq).2
  have hNotA : q ∉ (daiLiDGeKASubsystem P embedding d threshold w ell t).selected := by
    intro hA
    exact hOutside (Finset.mem_union_left _ hA)
  have hNotTrimmedB :
      q ∉ (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected := by
    intro hB
    exact hOutside (Finset.mem_union_right _ hB)
  rcases daiLiDGeK_assignment P embedding d threshold w ell t hGlobal hw hEll q with
      hSeparator | hA | hB
  · exact hSeparator
  · exact (hNotA hA).elim
  · exfalso
    apply hNotTrimmedB
    exact Finset.mem_sdiff.mpr ⟨hB, hNotA⟩
end QEC.Locality
