-- Prove2me | solution 1 for TunnellMap.bResidual_exists_unique_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:28:55.675264+00:00
-- url     : https://prove2.me/submissions/0553a009-757c-4c5d-bd4b-f18cf55cfa31

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_exists_unique_sign

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (x : BResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActB σ
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x :=
  (bResidualInvolution n).exists_unique_sign bResidualLexKey
    bResidualLexKey_injective x
end TunnellMap
