-- Prove2me | solution 1 for QEC.Coding.f256MFEpi2_sigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:53.648807+00:00
-- url     : https://prove2.me/submissions/6c031888-7486-40e4-880a-a129d2d23357

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

private theorem f256MFEpi2_apply (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by
  simp [f256MFEpi2, f256MFEIndex]

private theorem f256MFESigma_apply (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by
  simp [f256MFESigma, f256MFEIndex]

private theorem f256MFEPermutationAction_apply (pi : Equiv.Perm (Fin 512))
    (v : Fin 512 → ZMod 2) (q : Fin 512) :
    f256MFEPermutationAction pi v q = v (pi q) := rfl

theorem solution (y : F256) (i j k : Fin 8) :
    f256MFEpi2Action (f256MFESigma y) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun y j := by
  rw [f256MFEpi2Action, f256MFEPermutationAction_apply, f256MFEpi2_apply,
    f256MFESigma_apply]
