-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:09:03.359484+00:00
-- url     : https://prove2.me/submissions/a92369a6-2df2-40aa-84c2-4af9acd4a859

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyHeckeElement

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
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsFiniteHeckeElement a n).coeff 1 := by
  exact trace_cayleyHeckeElement (lpsQuaternionLabel a) (p : ℂ) n
end QEC.Coding.TannerLiftedProduct
