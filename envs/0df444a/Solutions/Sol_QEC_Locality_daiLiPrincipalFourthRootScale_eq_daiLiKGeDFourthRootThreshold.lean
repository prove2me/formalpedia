-- Prove2me | solution 1 for QEC.Locality.daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:30:00.372442+00:00
-- url     : https://prove2.me/submissions/d249795b-5942-4483-af85-af0fd16472dc

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (k d n : ℝ) (hk : 0 ≤ k) (hn : 0 < n) :
    daiLiPrincipalFourthRootScale k d n =
      daiLiKGeDFourthRootThreshold k d n := by
  unfold daiLiPrincipalFourthRootScale daiLiKGeDFourthRootThreshold
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  rw [daiLiFourthRoot, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hRatio]
  norm_num
  ring
end QEC.Locality
