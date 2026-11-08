-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_cayleyHeckeElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:04:17.913196+00:00
-- url     : https://prove2.me/submissions/eefa0726-8134-495a-8f3a-bf9649e0daae

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyRightRegularRepresentation_asAlgebraHom


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (p : ℂ) (n : ℕ) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyHeckeElement label p n)) =
      (Fintype.card G : ℂ) * (cayleyHeckeElement label p n).coeff 1 :=
  trace_cayleyRightRegularRepresentation_asAlgebraHom _
end QEC.Coding.TannerLiftedProduct
