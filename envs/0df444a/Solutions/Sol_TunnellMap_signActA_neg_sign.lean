-- Prove2me | solution 1 for TunnellMap.signActA_neg_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:40.159987+00:00
-- url     : https://prove2.me/submissions/5852e78c-69b1-4f49-9768-963b994f1fea

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_sign

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (y : AResidual n) :
    signActA hnpos (-σ) y = negAResidual (signActA hnpos σ y) :=
  (aResidualInvolution n hnpos).signAct_neg_sign hσ y
end TunnellMap
