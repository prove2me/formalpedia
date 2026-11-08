-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:07:28.030971+00:00
-- url     : https://prove2.me/submissions/36e44f42-ca02-4558-9b15-96940493046d

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_action

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
    cayleyRightRegularRepresentation.asAlgebraHom
        (lpsFiniteHeckeElement a n) =
      (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
        (algebraMap ℂ
          (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum (lpsQuaternionLabel a))) := by
  exact cayleyHeckeElement_action (lpsQuaternionLabel a) (p : ℂ) n
end QEC.Coding.TannerLiftedProduct
