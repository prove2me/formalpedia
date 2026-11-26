-- Prove2me | solution 1 for TunnellMap.mem_sourceRosterExec_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:39:45.309164+00:00
-- url     : https://prove2.me/submissions/ef799f2b-f750-425e-a917-40db60a60fc8

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
    (hx : canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x) :
    x ∈ sourceRosterExec n := by
  have hcanon : (bResidualInvolution n).canonicalPoint bResidualLexKey x = x := hx
  have hlt : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x) := by
    unfold FreeInvolution.canonicalPoint at hcanon
    by_cases h : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x)
    · exact h
    · rw [if_neg h] at hcanon
      exact absurd hcanon ((bResidualInvolution n).no_fixed x)
  refine (mem_sourceRosterExec_iff x).mpr ⟨x.1.2, ?_, ?_⟩
  · rw [← directSourceUsed_iff]; exact x.2
  · rw [tripleLexLtExec_iff]; exact hlt
end TunnellMap
