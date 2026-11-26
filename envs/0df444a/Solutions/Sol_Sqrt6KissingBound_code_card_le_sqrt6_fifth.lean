-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_sqrt6_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:32:37.591723+00:00
-- url     : https://prove2.me/submissions/397e7d68-5acf-48bc-871e-32fdf3d3bac8

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_code_card_le_eightyfive_dim_five

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 5)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 5 := by
  have hc : (X.card : ℝ) ≤ 85 := by exact_mod_cast code_card_le_eightyfive_dim_five X hunit hsep
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hs : (85 : ℝ) / 36 < Real.sqrt 6 := by
    apply (sq_lt_sq₀ (by norm_num) hs0).1
    rw [hsq]
    norm_num
  have h85 : (85 : ℝ) < (Real.sqrt 6) ^ 5 := by
    rw [show (Real.sqrt 6) ^ 5 = ((Real.sqrt 6) ^ 2) ^ 2 * Real.sqrt 6 by ring, hsq]
    nlinarith
  exact hc.trans h85.le
end Sqrt6KissingBound
