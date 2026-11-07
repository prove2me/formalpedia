-- Prove2me | solution 1 for QEC.Locality.daiLiPrincipalFourthRootScale_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:22:51.406554+00:00
-- url     : https://prove2.me/submissions/9443c2e0-15bc-406f-9e2d-afe1c33aa1a0

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition

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
    (k d n : ℝ) (hk : 0 ≤ k) (hn : 0 < n) :
    (daiLiPrincipalFourthRootScale k d n) ^ 4 =
      (1 / 100 : ℝ) ^ 4 * (k * d ^ 2 / n) := by
  have hRatio : 0 ≤ k * d ^ 2 / n := by
    exact div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  have hRoot := Real.rpow_inv_natCast_pow hRatio (by norm_num : (4 : ℕ) ≠ 0)
  unfold daiLiPrincipalFourthRootScale
  rw [mul_pow]
  convert congrArg (fun x : ℝ => (1 / 100 : ℝ) ^ 4 * x) hRoot using 1 <;>
    norm_num
end QEC.Locality
