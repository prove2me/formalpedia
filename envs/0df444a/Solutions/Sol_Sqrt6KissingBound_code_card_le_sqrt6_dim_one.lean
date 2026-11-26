-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_sqrt6_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:45.696979+00:00
-- url     : https://prove2.me/submissions/96dd1eaa-14c2-401f-bacb-c66863b994e6

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Theorems.Thm_Sqrt6KissingBound_code_card_le_two_dim_one

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) :
    (X.card : ℝ) ≤ Real.sqrt 6 := by
  have hc : (X.card : ℝ) ≤ 2 := by
    exact_mod_cast code_card_le_two_dim_one X hunit
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith
end Sqrt6KissingBound
