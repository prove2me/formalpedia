-- Prove2me | solution 1 for QEC.Coding.f256MFEPsi_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:20.435694+00:00
-- url     : https://prove2.me/submissions/8cec388c-9db5-4dd6-aa14-847b11294e04

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFE_ternary_reverse_mul

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Surjective f256MFEPsi := by
  intro x
  refine ⟨f256MFESigma x * f256MFEpi2Action (f256MFESigma 1) *
    f256MFEpi3Action (f256MFESigma 1), ?_⟩
  simpa using f256MFE_ternary_reverse_mul x 1 1
end QEC.Coding
