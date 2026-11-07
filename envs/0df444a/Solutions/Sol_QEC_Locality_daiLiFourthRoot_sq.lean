-- Prove2me | solution 1 for QEC.Locality.daiLiFourthRoot_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:22:10.718273+00:00
-- url     : https://prove2.me/submissions/c8ba86c7-2991-409c-9e58-380b1e7616e4

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution (x : ℝ) :
    daiLiFourthRoot x ^ 2 = Real.sqrt x := by
  unfold daiLiFourthRoot
  exact Real.sq_sqrt (Real.sqrt_nonneg x)
end QEC.Locality
