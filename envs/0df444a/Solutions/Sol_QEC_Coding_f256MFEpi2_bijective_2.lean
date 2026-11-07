-- Prove2me | solution 2 for QEC.Coding.f256MFEpi2_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:18.289424+00:00
-- url     : https://prove2.me/submissions/8f96ecb1-9308-44bd-8f5a-43b8acd3f679

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Bijective f256MFEpi2 :=
  f256MFEpi2.bijective
end QEC.Coding
