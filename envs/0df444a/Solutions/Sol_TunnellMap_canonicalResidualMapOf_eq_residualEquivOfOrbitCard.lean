-- Prove2me | solution 1 for TunnellMap.canonicalResidualMapOf_eq_residualEquivOfOrbitCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:34:58.633588+00:00
-- url     : https://prove2.me/submissions/3b39218b-7ac3-42d9-9025-7db3e7452d38

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_aResidualSign_mem
import Theorems.Thm_TunnellMap_aResidual_decomposition
import Theorems.Thm_TunnellMap_signedPartner_signActA
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_signedPartner
import Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_apply

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x =
      residualEquivOfOrbitCard hnpos hcard x := by
  classical
  rw [canonicalResidualMapOf_eq_signedPartner, residualEquivOfOrbitCard_apply]
  obtain ⟨o, ho⟩ : ∃ o, residualOrbitMatching hnpos hcard
      ((bResidualInvolution n).orbit x) = o := ⟨_, rfl⟩
  rw [ho]
  have hdec := aResidual_decomposition hnpos
    ((aResidualInvolution n hnpos).representative o)
  rw [(aResidualInvolution n hnpos).orbit_representative o] at hdec
  rw [← hdec, signedPartner_signActA hnpos (aResidualSign_mem hnpos _)]
end TunnellMap
