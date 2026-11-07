-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDFourthRootThreshold_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:23.130372+00:00
-- url     : https://prove2.me/submissions/c5a069af-b7bd-43aa-80b7-bfc94040e987

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_nonneg

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution (k d n : ℝ) :
    0 ≤ daiLiKGeDFourthRootThreshold k d n := by
  unfold daiLiKGeDFourthRootThreshold
  exact div_nonneg (daiLiFourthRoot_nonneg _) (by norm_num)
end QEC.Locality
