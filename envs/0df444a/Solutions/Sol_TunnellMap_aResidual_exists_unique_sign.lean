-- Prove2me | solution 1 for TunnellMap.aResidual_exists_unique_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:29:33.215903+00:00
-- url     : https://prove2.me/submissions/b49ac8b8-1259-490c-aea1-cbce0fed6d19

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_exists_unique_sign

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActA hnpos σ
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y :=
  (aResidualInvolution n hnpos).exists_unique_sign aResidualLexKey
    aResidualLexKey_injective y
end TunnellMap
