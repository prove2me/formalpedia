-- Prove2me | solution 1 for TunnellMap.canonical_of_mem_targetRosterExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:51:35.377904+00:00
-- url     : https://prove2.me/submissions/a2c62bda-eee2-4e6e-9977-392248b4eefb

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_mem_targetRosterExec_iff
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n} (hx : x ∈ targetRosterExec n) :
    canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x := by
  have h := (mem_targetRosterExec_iff x).mp hx
  have hlt : aResidualLexKey x <
      aResidualLexKey ((aResidualInvolution n hnpos).neg x) :=
    (tripleLexLtExec_iff x.1.1 (negTriple x.1.1)).mp h.2.2
  show (aResidualInvolution n hnpos).canonicalPoint aResidualLexKey x = x
  unfold FreeInvolution.canonicalPoint
  rw [if_pos hlt]
end TunnellMap
