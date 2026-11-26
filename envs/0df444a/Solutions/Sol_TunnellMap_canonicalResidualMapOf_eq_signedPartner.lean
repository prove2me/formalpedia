-- Prove2me | solution 1 for TunnellMap.canonicalResidualMapOf_eq_signedPartner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:12.416865+00:00
-- url     : https://prove2.me/submissions/07f8d295-eeea-4986-bb13-d5e53fd40891

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_bResidualSign_mem
import Theorems.Thm_TunnellMap_bResidual_decomposition
import Theorems.Thm_TunnellMap_etaPoint_signActB

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    canonicalResidualMapOf hnpos M x =
      signedPartner hnpos x
        (canonicalAResidualRepresentative hnpos
          (M ((bResidualInvolution n).orbit x))) := by
  obtain ⟨q, hq⟩ : ∃ q, (bResidualInvolution n).orbit x = q := ⟨_, rfl⟩
  have hσ : bResidualSign x = 1 ∨ bResidualSign x = -1 := bResidualSign_mem x
  have hx : signActB (bResidualSign x) (canonicalBResidualRepresentative q) = x := by
    rw [← hq]; exact bResidual_decomposition x
  have hkey : etaPoint x
      (canonicalAResidualRepresentative hnpos (M q)) =
      bResidualSign x *
        etaPoint (canonicalBResidualRepresentative q)
          (canonicalAResidualRepresentative hnpos (M q)) := by
    conv_lhs => rw [← hx]
    rw [etaPoint_signActB hσ]
  unfold canonicalResidualMapOf signedPartner canonicalEta
  rw [hq, hkey]
end TunnellMap
