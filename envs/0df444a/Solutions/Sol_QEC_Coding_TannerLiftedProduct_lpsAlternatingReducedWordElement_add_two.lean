-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:09:40.92153+00:00
-- url     : https://prove2.me/submissions/9ca33ecd-ea89-4a72-9904-7b3488a235e0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsAlternatingReducedWordElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsAlternatingReducedWordElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsAlternatingReducedWordElement a n := by
  have hrec :=
    cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one a n
  have hscalar :
      algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsAlternatingReducedWordElement a n =
        p • lpsAlternatingReducedWordElement a n := by
    rw [← Algebra.smul_def,
      Nat.cast_smul_eq_nsmul ℂ p]
  rw [hscalar]
  exact (eq_sub_iff_add_eq).2 hrec.symm
end QEC.Coding.TannerLiftedProduct
