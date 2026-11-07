-- Prove2me | solution 1 for QEC.Locality.daiLiFourthRoot_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:13:47.433882+00:00
-- url     : https://prove2.me/submissions/8b7e5a00-ec6a-42fa-8c8d-5f34501f16a9

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
    0 ≤ daiLiFourthRoot x :=
  Real.sqrt_nonneg _
end QEC.Locality
