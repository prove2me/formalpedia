-- Prove2me | solution 1 for ThreeSum.ReportingHostPairEnumeration.pairs_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:40.401199+00:00
-- url     : https://prove2.me/submissions/68a13b2a-a893-42bc-861f-9da231d1e157

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet



set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false
namespace ThreeSum.ReportingHostPairEnumeration
theorem _root_.solution {L h : ℕ} (p : Finset (Fin L) × Finset (Fin L)) :
    p ∈ pairs L h ↔ p ∈ edgeSet L h := by
  rw [LayerCounts.mem_edgeSet]
  constructor
  · intro hp
    obtain ⟨S,hS,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hp
    exact ⟨(lefts_mem S).mp hS,(rights_mem S R).mp hR⟩
  · rintro ⟨hS,hR,hd⟩
    exact List.mem_flatMap.mpr ⟨p.1,(lefts_mem p.1).mpr hS,
      List.mem_map.mpr ⟨p.2,(rights_mem p.1 p.2).mpr ⟨hR,hd⟩,rfl⟩⟩
end ThreeSum.ReportingHostPairEnumeration
