-- Prove2me | solution 1 for TunnellMap.RecordDA.terminalRun_held_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:40:18.883327+00:00
-- url     : https://prove2.me/submissions/d89f3506-cd6c-498d-ad64-063c637913d2

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_heldGenerated_terminalRun
import Theorems.Thm_TunnellMap_BlockGen_recordOf_sign_eq_etaPoint
import Theorems.Thm_TunnellMap_RecordDA_terminalRun_held


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    ∃ r : IncidentRecord,
      (terminalRun frames).held
          (orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q)) =
          some (canonicalBResidualRepresentative q, r) ∧
        r.target =
          orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q) ∧
        r.sign =
          canonicalEta hnpos q (residualOrbitMatching hnpos hcard q) := by
  obtain ⟨r, hheld, hrt, -⟩ := terminalRun_held hn hnpos frames hcard q
  refine ⟨r, hheld, hrt, ?_⟩
  have hmem := heldGenerated_terminalRun hn hnpos frames _ _ _ hheld
  obtain ⟨i, hi, rfl⟩ := (mem_fullTrace _ r).mp hmem
  have hret : Retained (canonicalBResidualRepresentative q)
      (frames (canonicalBResidualRepresentative q)) i :=
    (block_of_mem_validIndices _ hi).2.2.2
  exact recordOf_sign_eq_etaPoint hnpos _ hret hrt
end TunnellMap.RecordDA
