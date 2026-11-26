-- Prove2me | solution 1 for TunnellMap.canonical_of_mem_sourceRosterExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:39:08.463953+00:00
-- url     : https://prove2.me/submissions/02bcb8cd-4db0-40a8-89af-dbb597d8e90d

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_mem_sourceRosterExec_iff
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {x : BResidual n}
    (hx : x ∈ sourceRosterExec n) :
    canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by
  have h := (mem_sourceRosterExec_iff x).mp hx
  have hlt : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x) := by
    have := (tripleLexLtExec_iff x.1.1 (negTriple x.1.1)).mp h.2.2
    exact this
  show (bResidualInvolution n).canonicalPoint bResidualLexKey x = x
  unfold FreeInvolution.canonicalPoint
  rw [if_pos hlt]
end TunnellMap
