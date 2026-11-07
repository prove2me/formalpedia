-- Prove2me | solution 2 for QEC.Coding.f256MFEpi2_sigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:40.633934+00:00
-- url     : https://prove2.me/submissions/07560291-8f62-4353-a54d-d79481416d6e

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFEpi2_apply
import Theorems.Thm_QEC_Coding_f256MFESigma_apply
import Theorems.Thm_QEC_Coding_f256MFEPermutationAction_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (y : F256) (i j k : Fin 8) :
    f256MFEpi2Action (f256MFESigma y) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun y j := by
  rw [f256MFEpi2Action, f256MFEPermutationAction_apply, f256MFEpi2_apply,
    f256MFESigma_apply]
end QEC.Coding
