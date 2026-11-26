-- Prove2me | solution 1 for TunnellMap.sourceRosterExec_orbit_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:41:56.834018+00:00
-- url     : https://prove2.me/submissions/ee774b85-eb95-446b-aa9f-1b3442d098db

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_canonical_of_mem_sourceRosterExec
import Theorems.Thm_TunnellMap_mem_sourceRosterExec_of_canonical
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ}
    (q : (bResidualInvolution n).Orbit) :
    ∃! x : BResidual n, x ∈ sourceRosterExec n ∧
      (bResidualInvolution n).orbit x = q := by
  refine ⟨canonicalBResidualRepresentative q, ⟨?_, ?_⟩, ?_⟩
  · refine mem_sourceRosterExec_of_canonical ?_
    rw [orbit_canonicalBResidualRepresentative]
  · exact orbit_canonicalBResidualRepresentative q
  · rintro y ⟨hy, rfl⟩
    exact (canonical_of_mem_sourceRosterExec hy).symm
end TunnellMap
