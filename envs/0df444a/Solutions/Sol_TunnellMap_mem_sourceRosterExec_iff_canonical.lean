-- Prove2me | solution 1 for TunnellMap.mem_sourceRosterExec_iff_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:41:29.056524+00:00
-- url     : https://prove2.me/submissions/cf1ac0f9-a40d-45c9-87c0-f8510c1061bf

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_canonical_of_mem_sourceRosterExec
import Theorems.Thm_TunnellMap_mem_sourceRosterExec_of_canonical

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x :=
  ⟨canonical_of_mem_sourceRosterExec, mem_sourceRosterExec_of_canonical⟩
end TunnellMap
