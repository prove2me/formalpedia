-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:41:35.64966+00:00
-- url     : https://prove2.me/submissions/604db1dc-233f-48a9-85fc-5d2d32bc3058

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_hasPartiteExpanderMixingBound


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n degree : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral :=
  rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (lpsQuaternionFamilyLabel hp hp4 n) degree spectral
    hSpectralNonnegative hMixing
end QEC.Coding.TannerLiftedProduct
