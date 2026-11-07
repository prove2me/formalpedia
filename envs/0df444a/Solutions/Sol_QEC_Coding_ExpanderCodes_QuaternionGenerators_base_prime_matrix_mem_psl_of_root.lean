-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:26.196707+00:00
-- url     : https://prove2.me/submissions/7f5b61ae-21b4-4244-a908-ea06b4dc0308

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_base_prime_matrix_mem_psl_of_squares

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon r y s i : K)
    (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectiveBase epsilon y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectivePrime epsilon y hEpsilon hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  subst epsilon
  exact base_prime_matrix_mem_psl_of_squares r y s i hR hY hOne hTwo hRatio hI
end QEC.Coding.ExpanderCodes.QuaternionGenerators
