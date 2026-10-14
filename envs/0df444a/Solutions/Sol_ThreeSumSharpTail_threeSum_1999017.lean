-- Prove2me | solution 1 for ThreeSumSharpTail.threeSum_1999017
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T15:16:33.56778+00:00
-- url     : https://prove2.me/submissions/8c295241-d05d-4f1a-8854-2c0491f7b594

import Theorems.Thm_ThreeSumSharpTail_admissible_parameters_solve_3sum
import Theorems.Thm_ThreeSumSharpTail_explicit_parameter_certificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.999017 := by
  obtain ⟨henc, hprep, hquery, hprime, hbuild, hvalue, hmargin⟩ :=
    ThreeSumSharpTail.explicit_parameter_certificate
  apply ThreeSumSharpTail.admissible_parameters_solve_3sum
    21 0.11202 0.05665 0.06945 1.999017
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num at henc ⊢
    exact henc
  · norm_num at hprep ⊢
    exact hprep
  · norm_num at hquery ⊢
    exact hquery
  · norm_num at hprime ⊢
    exact hprime
  · norm_num at hbuild ⊢
  · norm_num

-- This is a reduction with two open platform children, not a closed proof.
