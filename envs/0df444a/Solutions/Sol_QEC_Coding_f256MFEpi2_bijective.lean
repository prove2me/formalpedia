-- Prove2me | solution 1 for QEC.Coding.f256MFEpi2_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:13.862993+00:00
-- url     : https://prove2.me/submissions/b560e6dc-d150-47f4-aac6-ed9ed0ab4ca0

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding
theorem solution : Function.Bijective f256MFEpi2 := f256MFEpi2.bijective
