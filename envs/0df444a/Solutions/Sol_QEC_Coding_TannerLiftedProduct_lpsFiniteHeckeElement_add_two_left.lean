-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:13:47.252788+00:00
-- url     : https://prove2.me/submissions/ad7bf1a5-035b-4fdf-9a89-bfdfe8087d87

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_commute_generatorSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_add_two


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsFiniteHeckeElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by
  rw [lpsFiniteHeckeElement_add_two]
  rw [(lpsFiniteHeckeElement_commute_generatorSum a (n + 1)).eq]
end QEC.Coding.TannerLiftedProduct
