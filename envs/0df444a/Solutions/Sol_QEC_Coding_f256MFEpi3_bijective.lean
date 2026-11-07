-- Prove2me | solution 1 for QEC.Coding.f256MFEpi3_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:14.619408+00:00
-- url     : https://prove2.me/submissions/62be6d3b-fee9-48b5-b29f-6e55338dcb65

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding
theorem solution : Function.Bijective f256MFEpi3 := f256MFEpi3.bijective
