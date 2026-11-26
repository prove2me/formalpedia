-- Prove2me | solution 1 for Sendov.finite_range_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:03.937493+00:00
-- url     : https://prove2.me/submissions/4f006798-defc-4f8c-8252-11a101d64559

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
import Theorems.Thm_Sendov_M_twenty
import Theorems.Thm_Sendov_A_twenty
import Theorems.Thm_P2M_Sendov_c_twenty__12ee6a925b10
import Theorems.Thm_Sendov_P_twenty_pos
import Theorems.Thm_Sendov_R_twenty_le
import Theorems.Thm_Sendov_alpha_le_half_M
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) (hfeas : c 20 α ^ 2 ≤ A 20 α) : R 20 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 19 / 2 := by
    have h := alpha_le_half_M (n := 20) (by norm_num) hfeas
    rw [M_twenty] at h
    linarith
  have hR := R_twenty_le hα
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 38 + 1 / (76 * (3 + α))
      + 1710 * A 20 α ^ 2 / (3 + α) * mom 20 α 8
      = 1 - (        2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
          7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496
          * α ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 -
          32607895082957507571 * α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10
          - 2640164743526400 * α ^ 11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 -
          2508597900288 * α ^ 14 - 62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 -
          33792 * α ^ 18)
          / (178855464872570772 * (3 + α) ^ 9) := by
    rw [mom, A_twenty, c_twenty' hα]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_one]
    norm_num
    field_simp
    ring
  rw [hid] at hR
  have hP := P_twenty_pos hα hle
  have hq : 0 < (      2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
        7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496 *
        α ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 -
        32607895082957507571 * α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10 -
        2640164743526400 * α ^ 11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 -
        2508597900288 * α ^ 14 - 62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 -
        33792 * α ^ 18)
      / (178855464872570772 * (3 + α) ^ 9) := div_pos hP (by positivity)
  linarith
end Sendov
