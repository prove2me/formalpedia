-- Prove2me | solution 1 for TunnellMap.directDomainExec_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:21.152867+00:00
-- url     : https://prove2.me/submissions/ae00d3a9-7d7f-4387-ac70-ac4e674942fa

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {p : BOddRep n} {d : DirectDomain n}
    (h : directDomainExec p = some d) : directDomainRep d = p := by
  unfold directDomainExec at h
  split_ifs at h <;> rw [← Option.some.inj h] <;> rfl
end TunnellMap
