-- Prove2me | solution 1 for QEC.Coding.f256SelfDualPInv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:15.321574+00:00
-- url     : https://prove2.me/submissions/d9bce1c3-944e-4d7d-88fc-073bed620d12

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
set_option autoImplicit false
open QEC QEC.Coding
theorem solution : f256SelfDualPInv * f256SelfDualP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide
