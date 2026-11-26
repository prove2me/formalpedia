-- Prove2me | solution 1 for TunnellMap.residualEquivOfOrbitCard_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:32:52.061781+00:00
-- url     : https://prove2.me/submissions/4edce73a-a038-44d2-86ee-4b4cd53b0305

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_signActA_neg_sign
import Theorems.Thm_TunnellMap_etaPoint_mem
import Theorems.Thm_TunnellMap_etaPoint_neg_source
import Theorems.Thm_TunnellMap_signedPartner_eq_preferredTarget
import Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_neg_representative
import Theorems.Thm_TunnellMap_residualEquivOfOrbitCard_representative


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    residualEquivOfOrbitCard hnpos hcard x =
      signedPartner hnpos x
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard
            ((bResidualInvolution n).orbit x))) := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, (bResidualInvolution n).orbit x = q := ⟨_, rfl⟩
  have hrel : x = (bResidualInvolution n).representative q ∨
      x = negBResidual ((bResidualInvolution n).representative q) :=
    (bResidualInvolution n).orbit_eq_iff.mp
      (((bResidualInvolution n).orbit_representative q).trans hq.symm)
  rw [hq]
  rcases hrel with hx | hx
  · rw [hx, residualEquivOfOrbitCard_representative hnpos hcard q,
      signedPartner_eq_preferredTarget]
  · rw [hx, residualEquivOfOrbitCard_neg_representative hnpos hcard q,
      ← signedPartner_eq_preferredTarget hnpos]
    unfold signedPartner
    rw [etaPoint_neg_source, signActA_neg_sign hnpos (etaPoint_mem _ _)]
end TunnellMap
