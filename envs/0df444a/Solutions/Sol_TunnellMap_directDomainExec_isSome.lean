-- Prove2me | solution 1 for TunnellMap.directDomainExec_isSome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:23.034002+00:00
-- url     : https://prove2.me/submissions/0c8f79ee-e2ad-4f20-b333-7e6782982c18

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {p : BOddRep n} (h : DirectSourceUsed p) :
    ∃ d : DirectDomain n, directDomainExec p = some d := by
  rw [directSourceUsed_iff] at h
  unfold directDomainExec
  split_ifs with h₁ h₂ h₃
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact absurd h (by
      unfold SourceUsedTriple
      push_neg
      exact ⟨h₁, h₂, h₃⟩)
end TunnellMap
