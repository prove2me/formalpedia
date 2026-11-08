-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:11:20.612436+00:00
-- url     : https://prove2.me/submissions/f7432d84-5b43-420f-8a4c-ed6f0ba50ec6

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (s g : G) (f : G → ℂ) :
    cayleyRightRegularRepresentation s f g = f (g * s) := rfl
end QEC.Coding.TannerLiftedProduct
