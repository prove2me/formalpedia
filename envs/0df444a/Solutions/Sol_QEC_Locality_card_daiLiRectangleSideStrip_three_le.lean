-- Prove2me | solution 1 for QEC.Locality.card_daiLiRectangleSideStrip_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:18:55.411262+00:00
-- url     : https://prove2.me/submissions/67d994d7-6c91-4e21-aa8f-ca5ce63a3d6d

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
    (hEll : 1 ≤ 2 * ell) (hLong : 1 ≤ upper.1 - lower.1 - 4 * ell) :
    ((daiLiRectangleSideStripQubits embedding ell lower upper 3).card : ℝ) ≤
      12 * ell * (upper.1 - lower.1 - 4 * ell) := by
  have h := embedding.card_qubitsInRectangle_le_six_mul_area
    (lower.1 + 2 * ell, upper.2 - ell)
    (upper.1 - 2 * ell, upper.2 + ell) (by linarith) (by linarith)
  change ((embedding.qubitsInRectangle
    (lower.1 + 2 * ell, upper.2 - ell)
    (upper.1 - 2 * ell, upper.2 + ell)).card : ℝ) ≤ _
  calc
    _ ≤ 6 * ((upper.1 - 2 * ell - (lower.1 + 2 * ell)) * (ell + ell)) := by
      convert h using 1 <;> norm_num
    _ = 6 * ((upper.1 - lower.1 - 4 * ell) * (2 * ell)) := by ring
    _ = _ := by ring
end QEC.Locality
