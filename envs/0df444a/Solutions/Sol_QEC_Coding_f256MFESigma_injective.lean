-- Prove2me | solution 1 for QEC.Coding.f256MFESigma_injective
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:54.456562+00:00
-- url     : https://prove2.me/submissions/2c56d030-3b23-4ed6-bf86-56d8f8b998e8

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

private theorem f256MFESigma_apply (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by
  simp [f256MFESigma, f256MFEIndex]

theorem solution : Function.Injective f256MFESigma := by
  intro x y hxy
  apply f256PolynomialBasis.equivFun.injective
  ext i
  have hcoordinate := congr_fun hxy (f256MFEIndex i 0 0)
  simpa only [f256MFESigma_apply] using hcoordinate
