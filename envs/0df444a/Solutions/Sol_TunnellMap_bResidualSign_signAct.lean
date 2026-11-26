-- Prove2me | solution 1 for TunnellMap.bResidualSign_signAct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:28:02.424961+00:00
-- url     : https://prove2.me/submissions/a935c20d-44dc-4405-bc27-0b3e0e2124e0

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_signAct

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (q : (bResidualInvolution n).Orbit) :
    bResidualSign (signActB σ (canonicalBResidualRepresentative q)) = σ :=
  (bResidualInvolution n).signOf_signAct bResidualLexKey
    bResidualLexKey_injective hσ q
end TunnellMap
