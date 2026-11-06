-- Prove2me | solution 1 for QEC.Locality.card_daiLiRectangleSideStrip_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:18:28.145092+00:00
-- url     : https://prove2.me/submissions/a06157da-125a-4c7c-912c-19f8c0f13c55

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_card_qubitsInRectangle_le_six_mul_area


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
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (lower upper : ℝ × ℝ)
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.2 - lower.2 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 0).card : ℝ) ≤
      12 * ell * (upper.2 - lower.2 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (lower.1 - ell, lower.2 + 2 * ell)
    (lower.1 + ell, upper.2 - 2 * ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (lower.1 - ell, lower.2 + 2 * ell)
    (lower.1 + ell, upper.2 - 2 * ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((ell + ell) * (upper.2 - 2 * ell - (lower.2 + 2 * ell))) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((2 * ell) * (upper.2 - lower.2 - 4 * ell)) := by ring
    _ = _ := by ring
end QEC.Locality
