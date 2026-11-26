-- Prove2me | solution 1 for TunnellMap.targetRosterExec_orbit_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:02:40.021804+00:00
-- url     : https://prove2.me/submissions/fc1a3801-df3f-4c50-9dc8-4829bdb9b797

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_canonical_of_mem_targetRosterExec
import Theorems.Thm_TunnellMap_mem_targetRosterExec_of_canonical
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (q : (aResidualInvolution n hnpos).Orbit) :
    ∃! x : AResidual n, x ∈ targetRosterExec n ∧
      (aResidualInvolution n hnpos).orbit x = q := by
  refine ⟨canonicalAResidualRepresentative hnpos q, ⟨?_, ?_⟩, ?_⟩
  · refine mem_targetRosterExec_of_canonical hnpos ?_
    rw [orbit_canonicalAResidualRepresentative]
  · exact orbit_canonicalAResidualRepresentative hnpos q
  · rintro y ⟨hy, rfl⟩
    exact (canonical_of_mem_targetRosterExec hnpos hy).symm
end TunnellMap
