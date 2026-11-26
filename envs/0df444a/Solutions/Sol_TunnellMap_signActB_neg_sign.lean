-- Prove2me | solution 1 for TunnellMap.signActB_neg_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:28:32.135375+00:00
-- url     : https://prove2.me/submissions/67321c01-50c6-41a7-9240-89026e0f9dcc

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_sign

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (x : BResidual n) :
    signActB (-σ) x = negBResidual (signActB σ x) :=
  (bResidualInvolution n).signAct_neg_sign hσ x
end TunnellMap
