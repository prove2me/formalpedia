-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveDegreeRootIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:45.523018+00:00
-- url     : https://prove2.me/submissions/df2752d5-3583-4a87-8c97-afcbf1e1254f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRootIndex a < a.q :=
  (Nat.find_spec (exists_lpsDegreeRootCandidate a)).1
end QEC.Coding.TannerLiftedProduct
