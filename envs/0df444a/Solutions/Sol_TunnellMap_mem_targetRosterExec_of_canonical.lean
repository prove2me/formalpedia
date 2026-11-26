-- Prove2me | solution 1 for TunnellMap.mem_targetRosterExec_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:51:41.28374+00:00
-- url     : https://prove2.me/submissions/c14997bb-2a7b-4341-ab68-d9efae34d029

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_mem_targetRosterExec_iff
import Theorems.Thm_TunnellMap_directTargetUsed_iff
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
attribute [local simp] TunnellMap.tripleLexLtExec_iff



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n}
    (hx : canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x) :
    x ∈ targetRosterExec n := by
  have hcanon : (aResidualInvolution n hnpos).canonicalPoint aResidualLexKey x = x := hx
  have hlt : aResidualLexKey x <
      aResidualLexKey ((aResidualInvolution n hnpos).neg x) := by
    unfold FreeInvolution.canonicalPoint at hcanon
    by_cases h : aResidualLexKey x <
        aResidualLexKey ((aResidualInvolution n hnpos).neg x)
    · exact h
    · rw [if_neg h] at hcanon
      exact absurd hcanon ((aResidualInvolution n hnpos).no_fixed x)
  refine (mem_targetRosterExec_iff x).mpr ⟨x.1.2, ?_, ?_⟩
  · rw [← directTargetUsed_iff]; exact x.2
  · rw [tripleLexLtExec_iff]; exact hlt
end TunnellMap
