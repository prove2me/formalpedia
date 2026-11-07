-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.base_prime_matrix_mem_psl_of_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:38.297098+00:00
-- url     : https://prove2.me/submissions/5b097f3c-f8df-409c-9715-429c43454a04

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveBase_matrix_mem_psl_iff
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_matrix_mem_psl_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (r y s i : K)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquiv r y hR hOne hTwo
          (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  constructor
  · exact (projectiveBase_matrix_mem_psl_iff r y hR hY hOne hTwo).mpr ⟨s, hRatio⟩
  · apply (projectivePrime_matrix_mem_psl_iff r y hR hY hOne hTwo).mpr
    refine ⟨i * r * s, ?_⟩
    rw [mul_pow, mul_pow, hI, hRatio]
    ring
end QEC.Coding.ExpanderCodes.QuaternionGenerators
