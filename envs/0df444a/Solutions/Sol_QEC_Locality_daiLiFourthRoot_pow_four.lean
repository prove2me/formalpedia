-- Prove2me | solution 1 for QEC.Locality.daiLiFourthRoot_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:18.111622+00:00
-- url     : https://prove2.me/submissions/f5cd3f8d-08be-40f2-b633-f57366ec9c87

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_sq

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) :
    daiLiFourthRoot x ^ 4 = x := by
  calc
    daiLiFourthRoot x ^ 4 = (daiLiFourthRoot x ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by rw [daiLiFourthRoot_sq x]
    _ = x := Real.sq_sqrt hx
end QEC.Locality
