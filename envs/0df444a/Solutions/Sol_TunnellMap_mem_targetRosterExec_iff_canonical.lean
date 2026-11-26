-- Prove2me | solution 1 for TunnellMap.mem_targetRosterExec_iff_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:33:43.721869+00:00
-- url     : https://prove2.me/submissions/269a9bb1-133f-4bf6-a9c9-a5d2d41d7edb

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_canonical_of_mem_targetRosterExec
import Theorems.Thm_TunnellMap_mem_targetRosterExec_of_canonical

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (x : AResidual n) :
    x ∈ targetRosterExec n ↔
      canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit x) = x :=
  ⟨canonical_of_mem_targetRosterExec hnpos, mem_targetRosterExec_of_canonical hnpos⟩
end TunnellMap
