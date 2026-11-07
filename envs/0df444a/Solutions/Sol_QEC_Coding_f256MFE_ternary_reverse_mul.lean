-- Prove2me | solution 1 for QEC.Coding.f256MFE_ternary_reverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:23.2634+00:00
-- url     : https://prove2.me/submissions/0919e8ad-2fee-4764-b263-a2cc9be9eb5e

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFESigma_apply
import Theorems.Thm_QEC_Coding_f256MFEPsi_apply
import Theorems.Thm_QEC_Coding_f256MFEpi2_sigma_apply
import Theorems.Thm_QEC_Coding_f256MFEpi3_sigma_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (x y z : F256) :
    f256MFEPsi (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
      f256MFEpi3Action (f256MFESigma z)) = x * y * z := by
  calc
    f256MFEPsi (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
        f256MFEpi3Action (f256MFESigma z)) =
        (∑ i : Fin 8, f256PolynomialBasis.equivFun x i • f256PolynomialBasis i) *
          (∑ j : Fin 8, f256PolynomialBasis.equivFun y j • f256PolynomialBasis j) *
          ∑ k : Fin 8, f256PolynomialBasis.equivFun z k • f256PolynomialBasis k := by
      rw [f256MFEPsi_apply]
      simp only [Pi.mul_apply, f256MFESigma_apply, f256MFEpi2_sigma_apply,
        f256MFEpi3_sigma_apply]
      rw [Fintype.sum_mul_sum]
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      simp only [Algebra.smul_def, map_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = x * y * z := by
      rw [f256PolynomialBasis.sum_equivFun x, f256PolynomialBasis.sum_equivFun y,
        f256PolynomialBasis.sum_equivFun z]
end QEC.Coding
