-- Prove2me | solution 1 for QEC.Coding.f256MFEpi3_sigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:54.069138+00:00
-- url     : https://prove2.me/submissions/519d3f72-011b-4a64-bf08-b9c1d5f49614

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

private theorem f256MFEpi2_apply (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by
  simp [f256MFEpi2, f256MFEIndex]

private theorem f256MFEpi3_apply (i j k : Fin 8) :
    f256MFEpi3 (f256MFEIndex i j k) = f256MFEIndex k i j := by
  rw [f256MFEpi3, Equiv.trans_apply, f256MFEpi2_apply, f256MFEpi2_apply]

private theorem f256MFESigma_apply (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by
  simp [f256MFESigma, f256MFEIndex]

private theorem f256MFEPermutationAction_apply (pi : Equiv.Perm (Fin 512))
    (v : Fin 512 → ZMod 2) (q : Fin 512) :
    f256MFEPermutationAction pi v q = v (pi q) := rfl

theorem solution (z : F256) (i j k : Fin 8) :
    f256MFEpi3Action (f256MFESigma z) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun z k := by
  rw [f256MFEpi3Action, f256MFEPermutationAction_apply, f256MFEpi3_apply,
    f256MFESigma_apply]
