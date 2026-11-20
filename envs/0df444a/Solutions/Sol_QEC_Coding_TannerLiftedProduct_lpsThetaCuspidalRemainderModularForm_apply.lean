-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainderModularForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:31:46.69369+00:00
-- url     : https://prove2.me/submissions/a40633b3-5346-42e3-a45c-78b8ca4c3e43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (z : ℍ) : lpsThetaCuspidalRemainderModularForm q hq2 z=
      lpsStandardTheta q z-lpsThetaEisensteinCorrection q hq2 z := rfl
end QEC.Coding.TannerLiftedProduct
