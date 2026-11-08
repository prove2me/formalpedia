-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:05:47.537198+00:00
-- url     : https://prove2.me/submissions/aaedd261-8752-474d-ad96-ad1acbfc6577

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_add_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]
open scoped MatrixGroups
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      lpsFiniteHeckeElement a (n + 1) *
          cayleyGeneratorSum (lpsQuaternionLabel a) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by
  exact cayleyHeckeElement_add_two (lpsQuaternionLabel a) (p : ℂ) n
end QEC.Coding.TannerLiftedProduct
