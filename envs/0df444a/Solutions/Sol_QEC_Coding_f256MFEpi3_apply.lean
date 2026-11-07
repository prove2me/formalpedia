-- Prove2me | solution 1 for QEC.Coding.f256MFEpi3_apply
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:53.133818+00:00
-- url     : https://prove2.me/submissions/df120bda-3b2f-4b63-8e38-7d43f8037b19

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

private theorem f256MFEpi2_apply (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by
  simp [f256MFEpi2, f256MFEIndex]

theorem solution (i j k : Fin 8) :
    f256MFEpi3 (f256MFEIndex i j k) = f256MFEIndex k i j := by
  rw [f256MFEpi3, Equiv.trans_apply, f256MFEpi2_apply, f256MFEpi2_apply]
