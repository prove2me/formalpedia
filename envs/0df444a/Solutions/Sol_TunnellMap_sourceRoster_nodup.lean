-- Prove2me | solution 1 for TunnellMap.sourceRoster_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:21.958581+00:00
-- url     : https://prove2.me/submissions/fd8b690a-35a1-43ca-b8b2-afbbd9791f49

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative



set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA
namespace TunnellMap
theorem _root_.solution : (sourceRoster n).Nodup := by
  rw [sourceRoster]
  refine List.Nodup.map_on ?_ residualSourceOrder_nodup
  intro q₁ _ q₂ _ heq
  rw [← orbit_canonicalBResidualRepresentative q₁, heq,
    orbit_canonicalBResidualRepresentative]
end TunnellMap
