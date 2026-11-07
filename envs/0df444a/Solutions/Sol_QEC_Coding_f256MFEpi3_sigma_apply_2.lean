-- Prove2me | solution 2 for QEC.Coding.f256MFEpi3_sigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:23.791843+00:00
-- url     : https://prove2.me/submissions/7cce06fd-6bfd-492a-b0d9-f5f2007ea318

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFEpi3_apply
import Theorems.Thm_QEC_Coding_f256MFESigma_apply
import Theorems.Thm_QEC_Coding_f256MFEPermutationAction_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (z : F256) (i j k : Fin 8) :
    f256MFEpi3Action (f256MFESigma z) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun z k := by
  rw [f256MFEpi3Action, f256MFEPermutationAction_apply, f256MFEpi3_apply,
    f256MFESigma_apply]
end QEC.Coding
