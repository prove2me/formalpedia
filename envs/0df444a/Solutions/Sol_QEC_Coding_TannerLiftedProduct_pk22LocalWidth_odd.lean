-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22LocalWidth_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:34.011494+00:00
-- url     : https://prove2.me/submissions/b9ceaaf8-4eaf-4710-ac4b-a15c36f0a144

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_odd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t : Nat) :
    Odd (pk22LocalWidth q t) := by
  exact (pk22ParameterBase_odd q t).pow
end QEC.Coding.TannerLiftedProduct
