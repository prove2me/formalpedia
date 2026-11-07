-- Prove2me | solution 2 for QEC.Coding.f256MFEpi3_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:19.336114+00:00
-- url     : https://prove2.me/submissions/49eedd8d-8331-4b38-9ba8-a55ddfbafdf8

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Bijective f256MFEpi3 :=
  f256MFEpi3.bijective
end QEC.Coding
