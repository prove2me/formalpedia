-- Prove2me | solution 1 for TunnellMap.aResidualSign_signAct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:29:35.628589+00:00
-- url     : https://prove2.me/submissions/6fe98eeb-fee3-4222-8f2d-e106661d5d12

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_signAct

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (o : (aResidualInvolution n hnpos).Orbit) :
    aResidualSign hnpos
        (signActA hnpos σ (canonicalAResidualRepresentative hnpos o)) = σ :=
  (aResidualInvolution n hnpos).signOf_signAct aResidualLexKey
    aResidualLexKey_injective hσ o
end TunnellMap
